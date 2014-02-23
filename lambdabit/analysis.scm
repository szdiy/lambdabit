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

(define-module (lambdabit analysis)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-26)
  #:use-module (lambdabit ast)
  #:use-module (lambdabit env)
  #:use-module (lambdabit primitives)
  #:use-module (lambdabit utils)
  #:export (mark-var!
            mark-needed-global-vars!
            needs-closure?
            toplevel-prc?
            side-effect-less?
            side-effect-oblivious?
            global-fv
            non-global-fv))
            
(define (mark-var! var)
  (when (and (var-global? var)
             (not (var-needed? var))
             ;; globals that obey the following condition are considered
             ;; to be constants
             ;; below fails if no definition (e.g. primitives), or mutable
             (not (cst? (var-val var))))
    (var-needed?-set! var #t)
    (let ((val (var-val var)))
      (when (and val (side-effect-less? val))
        (mark-needed-global-vars! val)))))

(define (mark-needed-global-vars! n)
  (match (->list n)
    (('ref _ () v)
     (mark-var! v))
    (('def _ (val) _)
     (when (not (side-effect-less? val))
       (mark-needed-global-vars! val)))
    ((or (? %cst?) (? %set?) (? %if*?) (? %prc?)
         (? %call?) (? %seq?))
     (for-each mark-needed-global-vars! (node-children n)))
    (else (compiler-error "mark-needed-global-vars!: unknown expression type" n))))

;; A lambda needs a closure if it has rest args, or if forced to because of
;; how one of its references uses it.
(define (needs-closure? v)
  (let ((proc (toplevel-prc? v)))
    (and proc
         (not (prc-rest? proc))
         (and-map (lambda (r)
                   (let ((parent (node-parent r)))
                     (and (call? parent)
                          (eq? (child1 parent) r)
                          (= (length (prc-params proc))
                             (- (length (node-children parent)) 1)))))
                 ;; may point to refs that are not in the program anymore
                 ;; this makes the analysis conservative, so we're safe
                 (var-refs v))
         proc)))

(define (toplevel-prc? v)
  ;; Since we don't have internal defines, the only way a variable can have
  ;; a val is to be defined at the toplevel. Otherwise, it would be lambda
  ;; -bound, in which case it has no val.
  (let ((val (var-val v))) ; non-false implies immutable
    (and (prc? val)
         val)))

;; FIXME: frankly, I don't like these code, they are not well modulerized.
;; oblivious? is true if we want to check for side-effect obliviousless, which
;; is stronger
(define* (side-effect-less? n #:optional (oblivious? #f) (seen '()))
  (and (or (cst? n) (prc? n) ; values
           ;; mutable var references are side-effect-less, but not oblivious
           (and (ref? n)
                (not (and oblivious? (mutable-var? (ref-var n)))))
           (and (or (seq? n) (if*? n))
                (every (lambda (x) 
                         (and x (side-effect-less? x oblivious? seen)))
                       (node-children n)))
           (and (call? n)
                (every (lambda (x)
                         (and x (side-effect-less? x oblivious? seen)))
                       (cdr (node-children n))) ; args
                (let ((op (car (node-children n))))
                  (cond 
                   ((prc? op)
                    (side-effect-less? oblivious? (child1 op))) ; body
                   ((ref? op)
                    (or (let* ((v (ref-var op))
                               (p (var-primitive v)))
                          ;; has a folder implies side-effect-less?
                          (and p (primitive-constant-folder p)
                               ;; for obliviousness, we also need it not to
                               ;; access mutable state
                               (if oblivious?
                                   (not (any (lambda (x) (var=? x v))
                                             mutable-data-accessors))
                                   #t)))
                        (let* ((v (ref-var op))
                               (val (var-val v))) ; non-false -> immutable
                          ;; refers to a side-effect-less? proc
                          ;; to avoid non-termination, we reject recursive funs
                          ;; Note: we could chase references further.
                          ;; we currently refet a ref to a ref of a
                          ;; side-effect-less? proc
                          (and (prc? val)
                               (not 
                                (any 
                                 (lambda (x)
                                   (and x 
                                        (if (var=? x v)
                                            (side-effect-less? (child1 val) ; body
                                                               oblivious?
                                                               (cons var seen)))))
                                 seen))))))))))))

;; could look into if*, seq, etc in operator position, making sure it refers to
;; a side-effect-less? proc (refs encountered during that are not automatically
;; ok)

;; The result of this expression does not depend on other side effects.
;; Implies: side-effect-less?
;; Corollary: this expression can be moved.
(define (side-effect-oblivious? n)
  (side-effect-less? n #t))

;; Free variable analysis.

;; These two are for outside consumption, so they return results as lists.
(define (global-fv n)
  ;;(format #t "global-fv: enter! ~a~%" n)
  (filter var-global? (fv n)))
(define (non-global-fv n)
  ;;(format #t "non-global-fv: enter! ~a~%" n)
  (filter (lambda (x) (not (var-global? x)))
          (fv n)))

(define (fv n)
  ;;(format #t "fv0: ~a~%" (->list n))
  (match (->list n)
    ((? %cst?)
    ;; (display "0\n")
     '()) ; empty varset
    (('ref _ () v)
     ;;(display "1\n")
     ;;(format #t "fv1: ~a~%" (->list v))
     (list v)) ; singleton varset
    (('def _ (val) v)
     ;;(display "2\n")
     ;;(format #t "fv2: ~a~%" v)
     (append (fv val) (if (list? v) v (list v))))
    (('set _ (val) v)
     ;;(display "3\n")
     ;;(format #t "fv3: ~a" v)
     (append (fv val) (if (list? v) v (list v))))
    (('prc _ (body) params _ _)
     ;;(display "4\n")
     (set-subtract (fv body) params))
    ((or (? %if*?) (? %call?) (? %seq?))
     ;;(format #t "fv: ~a~%" (map fv (node-children n)))
     (apply lset-union equal? (map fv (node-children n))))
    (else (compiler-error "fv: unknown expression type" n))))
