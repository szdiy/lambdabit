;;  Copyright (C) 2013,2014
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
  #:use-module (rnrs records syntactic)
  #:use-module (rnrs records procedural)
  #:use-module (rnrs records inspection)
  #:use-module (ice-9 control)
  #:use-module (ice-9 regex))

;; (use-modules (lambdabit utils) (lambdabit comp) (lambdabit reader) (lambdabit parser) (lambdabit ir) (lambdabit env) (lambdabit asm) (lambdabit analysis) (lambdabit back-end) (lambdabit code-gen) (lambdabit primitives) (lambdabit sched) (lambdabit compile) (lambdabit assembler) (lambdabit front-end) (lambdabit ast))
(module-export-all! (current-module))

(define-syntax-rule (-? o) 
  (lambda (x) (and (list? x) (eq? (car x) o))))

(define *pred-list*
  '(cst ref prc if* call seq def set))

(define (gen-inner-pred)
  (for-each (lambda (n)
              (module-define! (current-module) (symbol-append '% n '?) (-? n)))
            *pred-list*))

(gen-inner-pred)

(define (->list node) (and node (record->list node)))

(define* (record->list record #:optional (alist #f))
  (define (record-ref rtd k)
    ((record-accessor rtd k) record))
  (define (gen-val rtd k i)
    (let ((v (record-ref rtd i)))
      (if alist
          (cons k v)
          v)))
  (let* ((rtd (record-rtd record))
         (p (record-type-parent rtd))
         (name (record-type-name rtd))
         (pfields (if p (vector->list (record-type-field-names p)) '()))
         (plen (if p (length pfields) 0))
         (fields (vector->list (record-type-field-names rtd)))
         (len (length fields)))
    (append `(,name 
              ,@(map (lambda (k i) (gen-val p k i)) pfields (iota plen))
              ,@(map (lambda (k i) (gen-val rtd k i)) fields (iota len))))))

(define-syntax get-file-ext               
  (syntax-rules ()
    ((_ filename)
     (substring/shared filename
                       (1+ (string-index-right filename #\.))))))

(define (set-subtract s1 s2) (lset-difference equal? s1 s2))

(define (hash->list ht) (hash-map->list cons ht))

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

(define-syntax genid
  (syntax-rules ()
    ((_ name prefix)
     (gensym (string-append (object->string prefix) (object->string name))))
    ((_ prefix)
     (gensym (object->string prefix)))
    ((_) (gensym))))

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
  (cond
   ((list? lst)
    (apply values (map list lst (iota (length lst)))))
   ((integer? lst)
    (apply values (map list (iota lst) (iota lst))))))

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
(define current-libpath (make-parameter "lambdabit"))
(define default-outfile (make-parameter "a.hex"))

(define-syntax-rule (->lib file)
  (format #f "~a/~a" (current-libpath) file))
