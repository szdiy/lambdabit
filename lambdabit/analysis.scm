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
  #:use-module (lambdabit ast)
  #:use-module (lambdabit env)
  #:use-module (lambdabit primitives)
  #:use-module (lambdabit utils))

(module-export-all! (current-module))

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

(define (mark-needed-global-vars! node)
  (match (->list node)
    (('ref _ () var)
     (mark-var! var))
    (('def _ (val) _)
     (when (not (side-effect-less? val))
       (mark-needed-global-vars! val)))
    ((or (? %cst?) (? %set?) (? %if*?) (? %prc?)
         (? %call?) (? %seq?))
     (for-each mark-needed-global-vars! (node-children node)))
    (else (compiler-error "mark-needed-global-vars!: unknown expression type" node))))

;; A lambda needs a closure if it has rest args, or if forced to because of
;; how one of its references uses it.
(define (needs-closure? var)
  (let ((prc (toplevel-prc? var)))
    (and prc
         (not (prc-rest? prc))
         (and-map (lambda (r)
                   (let ((parent (node-parent r)))
                     (and (call? parent)
                          (eq? (child1 parent) r)
                          (= (length (prc-params prc))
                             (- (length (node-children parent)) 1)))))
                 ;; may point to refs that are not in the program anymore
                 ;; this makes the analysis conservative, so we're safe
                 (var-refs var))
         prc)))

(define (toplevel-prc? var)
  ;; Since we don't have internal defines, the only way a variable can have
  ;; a val is to be defined at the toplevel. Otherwise, it would be lambda
  ;; -bound, in which case it has no val.
  (let ((val (var-val var))) ; non-false implies immutable
    (and (prc? val)
         val)))

;; oblivious? is true if we want to check for side-effect obliviousless, which
;; is stronger
(define* (side-effect-less? node #:optional (oblivious? #f) (seen '()))
  (and (or (cst? node) (prc? node) ; values
           ;; mutable var references are side-effect-less, but not oblivious
           (and (ref? node)
                (not (and oblivious? (mutable-var? (ref-var node)))))
           (and (or (seq? node) (if*? node))
                (every (lambda (x) 
                         (and x (side-effect-less? x oblivious? seen)))
                       (node-children node)))
           (and (call? node)
                (every (lambda (x)
                         (and x (side-effect-less? x oblivious? seen)))
                       (cdr (node-children node))) ; args
                (let ((op (car (node-children node))))
                  (cond 
                   ((prc? op)
                    (side-effect-less? oblivious? (child1 op))) ; body
                   ((ref? op)
                    (or (let* ((var  (ref-var op))
                               (prim (var-primitive var)))
                          ;; has a folder implies side-effect-less?
                          (and prim (primitive-constant-folder prim)
                               ;; for obliviousness, we also need it not to
                               ;; access mutable state
                               (if oblivious?
                                   (not (any (lambda (x) (var=? x var))
                                             mutable-data-accessors))
                                   #t)))
                        (let* ((var (ref-var op))
                               (val (var-val var))) ; non-false -> immutable
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
                                        (if (var=? x var)
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
(define (side-effect-oblivious? node)
  (side-effect-less? node #t))

;; Free variable analysis.

;; These two are for outside consumption, so they return results as lists.
(define (global-fv node)
  (filter var-global? (fv node)))
(define (non-global-fv node)
  (filter (lambda (x) (not (var-global? x)))
          (fv node)))

(define (fv node)
  (match (->list node)
    ((? %cst?)
     '()) ; empty varset
    (('ref _ () var)
     (list var)) ; singleton varset
    (('def _ (val) var)
     (append (fv val) var))
    (('set _ (val) var)
     (append (fv val) var))
    (('prc _ (body) params _ _)
     (set-subtract (fv body) (map ->list params)))
    ((or (? %if*?) (? %call?) (? %seq?))
     (apply lset-union equal? (map fv (node-children node))))
    (else (compiler-error "fv: unknown expression type" node))))
