;;  Copyright (C) 2013
;;      "Mu Lei" known as "NalaGinrut" <NalaGinrut@gmail.com>
;;  This file is free software: you can redistribute it and/or modify
;;  it under the terms of the GNU General Public License as published by
;;  the Free Software Foundation, either version 3 of the License, or
;;  (at your option) any later version.

;;  This file is distributed in the hope that it will be useful,
;;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;  GNU General Public License for more details.

;;  You should have received a copy of the GNU General Public License
;;  along with this program.  If not, see <http://www.gnu.org/licenses/>.

(define-module (lambdabit utils)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-4)
  #:use-module (srfi srfi-41)
  #:use-module (ice-9 control)
  #:use-module (ice-9 regex)
  #:export (reset))

(module-export-all! (current-module))

(define (set-subtract s1 s2) (lset-difference equal? s1 s2))

(define (hash->list ht) (hash-map->list cons ht))

(define (get-the-file args) 
  (unless (< (length args) 2)
    (last args)
    (error get-the-file "Please specify a valid file!")))

(define-syntax-rule (begin0 expr body ...)
  (call-with-values
      (lambda () expr)
    (lambda args
      body ...
      (apply values args))))

(define (hash-update! t k up d)
  (let ((vv (hash-ref t k)))
    (if vv 
        (hash-set! t k (up vv))
        (hash-set! t k d))))

(define (in-naturals) (stream-iterate 1+ 0))

(define (get-all-exprs-from-port port)
  (let lp((expr (read port)) (ret '()))
    (cond
     ((eof-object? expr) (reverse ret))
     (else (lp (read port) (cons expr ret))))))

(define get-bytevector-all (@ (rnrs) get-bytevector-all))
(define get-string-all (@ (rnrs) get-string-all))

(define* (genid #:optional (prefix #f))
  (if prefix
      (gensym (object->string prefix))
      (gensym)))

(define* (regexp-split regex str #:optional (flags 0))
  (let ((ret (fold-matches 
              regex str (list '() 0 str)
              (lambda (m prev)
                (let* ((ll (car prev))
                       (start (cadr prev))
                       (tail (match:suffix m))
                       (end (match:start m))
                       (s (substring/shared str start end))
                       (groups (map (lambda (n) (match:substring m n))
                                    (iota (1- (match:count m)) 1))))
                  (list `(,@ll ,s ,@groups) (match:end m) tail)))
              flags)))
    `(,@(car ret) ,(caddr ret))))

(define (build-list n proc) (map proc (iota n)))

(define (set-union . lst)
  (apply lset-union equal? lst))

(define-syntax-rule (remq e lst)
  (remove (lambda (x) (eq? e x)) lst))

(define (specfied? x) (not (unspecified? x)))
 
(define* (range from to #:optional (step 1))
  (iota (- to from) from step))

(define (either lst) (shift k (for-each k lst)))

(define (either-val lst) (shift k (map k lst)))

(define (in-indexed lst)
  (apply values (either-val (map list lst (iota (length lst))))))

(define (compiler-error msg . others)
  (parameterize ((current-output-port (current-error-port)))
    (format #t "*** PICOBIT ERROR -- ~a" msg)
    (for-each (lambda (x) (format #t " ==> ~a~%" x)) others)
    (exit 1)))

(define (self-eval? expr)
  (or (number?   expr)
      (char?     expr)
      (boolean?  expr)
      (string?   expr)
      (u8vector? expr)))

;; to control output level
(define need-help (make-parameter #f))
(define show-size (make-parameter #f))
(define show-parsed (make-parameter #f))
(define show-front (make-parameter #f))
(define print-asm (make-parameter #f))
(define show-status (make-parameter #f))
(define outfile (make-parameter #f))
