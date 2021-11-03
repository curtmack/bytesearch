#!/usr/bin/guile \
-e main -s
!#

;; SPDX-License-Identifier: FSFAP
;; GNU All-Permissive License.  Copyright and license text at end of file.

(define (print-usage progname)
  (format #t "\
Usage: ~a <filename> <specs...>

Each spec reads a value and passes or fails.  Each spec takes a previous value M
and an argument N.  The previous value for the first spec is 0.

 +N -- Pass if the read value is N more than M.
 -N -- Pass if the read value is N less than M.
 =N -- Pass if the read value is exactly N.
 .N -- Read N values.  Always pass.
 ,N -- Skip N values without updating previous value.  Always pass.

For every byte offset in <filename> where every spec passes, the offset (in hex)
and a list of the bytes read (in hex) are reported.

As described, each spec reads a single-byte value.  Repeat prefix character for
the number of bytes you want to read (e.g. ==N to read a 16-bit value and
compare to N).  Prefix with `b' or `l' to force big- or little-endian; default
is big-endian.

Numbers can be specified in octal, hex, or binary with `o' / `x' / `b' prefix.
If no number is given, the default is 1 for the `,' or `.' specs, and 0 for
every other spec.~%" progname))

(use-modules (ice-9 format)
             (ice-9 binary-ports)
             (ice-9 regex)
             (srfi srfi-1)
             (srfi srfi-11)
             ((rnrs)
              #:version (6)
              #:select (mod)))

;; A specification to read some number of values from the input file, keeping
;; the last as the prev-value for the next spec.  Always passes.
(define (read-spec endian arity num)
  (when (not num)
    (set! num 1))
  (lambda (msg . args)
    (case msg
      [(#:endian) endian]
      [(#:arity) arity]
      [(#:count) num]
      [(#:check)
       (let ([vals (cdr args)])
         (values #t (last vals)))])))

;; A specification to skip some number of values from the input file, preserving
;; the last prev-value for the next spec.  Always passes.
(define (skip-spec endian arity num)
  (when (not num)
    (set! num 1))
  (lambda (msg . args)
    (case msg
      [(#:endian) endian]
      [(#:arity) arity]
      [(#:count) num]
      [(#:check)
       (let ([prev (first args)])
         (values #t prev))])))

;; A specification to compare one value to the prev-value.  Passes if the
;; difference between them is exactly as prescribed by the spec.
(define (rel-spec endian arity difference)
  (when (not difference)
    (set! difference 0))
  (lambda (msg . args)
    (case msg
      [(#:endian) endian]
      [(#:arity) arity]
      [(#:count) 1]
      [(#:check)
       (let ([prev (first args)]
             [val  (second args)])
         (values (= val (+ prev difference))
                 val))])))

;; A specification to compare one value against a constant value.  Passes if
;; these values are equal.
(define (eql-spec endian arity num)
  (when (not num)
    (set! num 0))
  (lambda (msg . args)
    (case msg
      [(#:endian) endian]
      [(#:arity) arity]
      [(#:count) 1]
      [(#:check)
       (let ([val (second args)])
         (values (= val num) val))])))

;; A mapping of type characters to spec classes.
(define spec-type-alist
  `((#\. . ,read-spec)
    (#\, . ,skip-spec)
    (#\= . ,eql-spec)
    (#\+ . ,rel-spec)
    (#\- . ,(lambda (endian arity num)
              (rel-spec endian arity (if num (- num) #f))))))

;; The regexp used for parsing specs.
(define spec-regexp
  (make-regexp
   "^([blBL]?)([\\+=\\.,-]+)([xobdXOBD]?)([0-9]*)$"))

;; Returns true if `str' is empty, or if every character in `str' is equal to
;; every other character.
(define (string-monotonic? str)
  (if (zero? (string-length str))
      #t
      (string-every
       (lambda (c) (char=? c (string-ref str 0)))
       str 1)))

;; Parse the spec given by `str'.
(define (parse-spec str)
  (let ([m (regexp-exec spec-regexp str)])
    (if m
        (let ([endian-str (match:substring m 1)]
              [type-str   (match:substring m 2)]
              [radix-str  (match:substring m 3)]
              [num-str    (match:substring m 4)])
          ;; Require the whole type-str to use the same type char throughout
          (unless (string-monotonic? type-str)
            (error (format #f "Unrecognized spec: ~a" str)))
          ;; Parse all components into their final forms
          (let* ([endian (if (string-ci=? endian-str "l")
                             #:little
                             #:big)]
                 [type   (string-ref type-str 0)]
                 [arity  (string-length type-str)]
                 [radix  (if (zero? (string-length radix-str))
                             ""
                             (string-append "#" radix-str))]
                 [num    (string->number
                          (string-append radix num-str))]
                 [spec   (assoc-ref spec-type-alist type)])
            ;; Return the actual spec
            (spec endian arity num)))
        ;; No match
        (error (format #f "Unrecognized spec: ~a" str)))))

;; Return the number of bytes needed for `spec'.
(define (spec-byte-length spec)
  (* (spec #:arity)
     (spec #:count)))

;; Return the total number of bytes needed for a spec list.
(define (specs-byte-length specs)
  (fold
   (lambda (spec accum) (+ accum (spec-byte-length spec)))
   0
   specs))

;; Get the next index after `index' in `buffer'
(define (circular-buffer-1+ buffer index)
  (mod (1+ index)
       (array-length buffer)))

;; Take `n' bytes from the circular buffer `buffer' starting at `start'.
;; Returns that list and the next index after those bytes as two values.
(define (take-from-circular-buffer buffer start n)
  (let recur ([accum '()]
              [current start]
              [remn n])
    (if (<= remn 0)
        (values (reverse! accum) current)
        (recur (cons (array-ref buffer current) accum)
               (circular-buffer-1+ buffer current)
               (1- remn)))))

;; Parse the list of unsigned octets `bytes' as an unsigned `endian' integer.
(define (endian-u endian bytes)
  (let recur ([accum 0]
              [bytes (case endian
                       [(#:big) bytes]
                       [(#:little) (reverse bytes)])])
    (if (null? bytes)
        accum
        (recur (+ (* 256 accum) (car bytes))
               (cdr bytes)))))

;; Parse the list of `arity'×N bytes into a list of N unsigned `arity'-byte
;; `endian' integers.
(define (unfold-arity lst endian arity)
  (let recur ([accum '()]
              [lst lst])
    (if (null? lst)
        (reverse! accum)
        (let ([group (take lst arity)]
              [remn  (drop lst arity)])
          (recur (cons (endian-u endian group) accum)
                 remn)))))

;; Check if the current circular buffer of bytes `buffer' starting at the index
;; `start' matches the list of specs `specs'.
(define (check-specs buffer start specs)
  (let recur ([specs      specs]
              [last-value 0]
              [current    start])
    (if (null? specs)
        #t
        (let ([spec       (car specs)]
              [remn-specs (cdr specs)])
          (let*-values ([(bytes next-index)
                         (take-from-circular-buffer
                          buffer
                          current
                          (spec-byte-length spec))]
                        [(vals)
                         (unfold-arity bytes (spec #:endian) (spec #:arity))]
                        [(success? next-value)
                         (apply spec #:check last-value vals)])
            (if success?
                (recur remn-specs next-value next-index)
                #f))))))

;; Print a match found in the circular buffer `buffer' starting at index `start'
;; at offset `offset' within the file.
(define (report-match offset buffer start)
  (format (current-output-port)
          "Found match at offset ~x, bytes: ~a~%"
          offset
          (map
           (lambda (byte) (string-pad (number->string byte 16) 2 #\0))
           (take-from-circular-buffer buffer start (array-length buffer)))))

;; Given the list of specs `specs', return a stateful lambda that takes a single
;; byte at a time, looking for spec matches.  It will report the matches it
;; finds to (current-output-port) without any intervention.
(define (make-searcher specs)
  (let* ([len        (specs-byte-length specs)]
         [buffer     (make-array 0 len)]
         [start      0]
         [bytes-read 0])
    (lambda (byte)
      ;; Insert byte into circular buffer
      (array-set! buffer byte start)
      (set! start (circular-buffer-1+ buffer start))
      ;; Increment bytes-read
      (set! bytes-read (1+ bytes-read))

      (when (and (>= bytes-read len)
                 (check-specs buffer start specs))
        (report-match (- bytes-read len)
                      buffer start)))))

;; Main entrypoint
(define (main args)
  (if (< (length args) 3)
      (print-usage (first args))
      (let ([filename (second args)]
            [specs (map parse-spec (cddr args))])
        (with-input-from-file filename
          (lambda ()
            (let recur ([searcher (make-searcher specs)])
              (let ([byte (get-u8 (current-input-port))])
                (if (eof-object? byte)
                    #t
                    (begin
                      (searcher byte)
                      (recur searcher))))))
          #:binary #t))))

;; Copyright 2021, Curtis Mackie

;; Copying and distribution of this file, with or without modification, are
;; permitted in any medium without royalty provided the copyright notice and
;; this notice are preserved. This file is offered as-is, without any warranty.
