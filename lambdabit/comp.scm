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

;; This module is used to compute the node to generate inner struct

(define-module (lambdabit comp)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-4)
  #:use-module (srfi srfi-11)
  #:use-module (ice-9 match)
  #:use-module (lambdabit analysis)
  #:use-module (lambdabit env)
  #:use-module (lambdabit ast)
  #:use-module (lambdabit code-gen)
  #:use-module (lambdabit ir)
  #:use-module (lambdabit utils)
  #:export (comp-node))

(define (comp-node node ctx)
  (match (->list node)
    ((or (? %cst?) (? %ref?) (? %prc?))
     ctx) ; we can drop any of these if we don't care about their value
    (('def _ (rhs) var)
     (if (needs-closure? var)
         (comp-prc rhs #f ctx)
         (if (var-needed? var)
             (let ((ctx2 (comp-push rhs ctx)))
               (gen-set-global (var-bare-id var) ctx2))
             (comp-node rhs ctx))))
    (('set _ (rhs) var)
     (if (var-needed? var)
         (let ((ctx2 (comp-push rhs ctx)))
           (gen-set-global (var-bare-id var) ctx2))
         (comp-node rhs ctx)))
    ((? %if*?)
     (comp-if node 'none ctx))
    ((? %call?)
     (comp-call node 'none ctx))
    ((? %seq?)
     (comp-seq node 'none ctx))
    (else (compiler-error "comp-node: unknown expression type" node))))

(define (comp-tail node ctx)
  (match (->list node)
    ((or (? %cst?) (? %ref?) (? %def?) (? %set?) (? %prc?))
     (gen-return (comp-push node ctx)))
    ((? %if*?)
     (comp-if node 'tail ctx))
    ((? %call?)
     (comp-call node 'tail ctx))
    ((? %seq?)
     (comp-seq node 'tail ctx))
    (else (compiler-error "comp-tail: unknown expression type" node))))

(define (comp-push node ctx)
  (match (->list node)
    (('cst _ () val)
     (gen-push-constant val ctx))
    (('ref _ () var)
     (cond 
      ((not (var-global? var)) ; not a global var, get from local
       (gen-push-local-var (var-bare-id var) ctx))
      ((var-def var) ; var was defined
       (let ((val (var-val var))) ; non-false implies immutable
         (if (cst? val) ; immutable global, counted as cst
             (gen-push-constant (cst-val val) ctx)
             (gen-push-global (var-bare-id  var) ctx))))
       (else (compiler-error "comp-push: undefined variable:" (var-id var)))))
    ((or (? %def?) (? %set?))
     (gen-push-unspecified (comp-node node ctx)))
    ((? %if*?)
     (comp-if node 'push ctx))
    ((? %prc?)
     (comp-prc node #t ctx))
    ((? %call?)
     (comp-call node 'push ctx))
    ((? %seq?)
     (comp-seq node 'push ctx))
    (else (compiler-error "comp-push: unknown expression type" node))))

(define (comp-if node reason ctx)
  (match (->list node)
    (('if* _ (tst thn els))
     (case reason
       ((none push)
        (let*-values
            (((rec-comp) (if (eq? reason 'none) comp-node comp-push))
             ((ctx2 label-then) (context-make-label ctx))
             ((ctx3 label-else) (context-make-label ctx2))
             ((ctx4 label-then-join) (context-make-label ctx3))
             ((ctx5 label-else-join) (context-make-label ctx4))
             ((ctx6 label-join) (context-make-label ctx5))
             ((ctx7) (comp-test tst label-then label-else ctx6))
             ((ctx8) (gen-goto
                      label-else-join
                      (rec-comp els (context-change-env2
                                     (context-add-bb ctx7 label-else)
                                     #f))))
             ((ctx9) (gen-goto
                      label-then-join
                      (rec-comp thn (context-change-env
                                     (context-add-bb ctx8 label-then)
                                     (context-env2 ctx7)))))
             ((ctx10) (gen-goto
                       label-join
                       (context-add-bb ctx9 label-else-join)))
             ((ctx11) (gen-goto
                       label-join
                       (context-add-bb ctx10 label-then-join)))
             ((ctx12) (context-add-bb ctx11 label-join)))
          ctx12))
       ((tail)
        (let*-values
         (((ctx2 label-then) (context-make-label ctx))
          ((ctx3 label-else) (context-make-label ctx2))
          ((ctx4) (comp-test tst label-then label-else ctx3))
          ((ctx5) (comp-tail els
                             (context-change-env2
                              (context-add-bb ctx4 label-else)
                              #f)))
          ((ctx6) (comp-tail thn
                             (context-change-env
                              (context-add-bb ctx5 label-then)
                              (context-env2 ctx4)))))
       ctx6))))))

(define (comp-seq node reason ctx)
  (match (->list node)
    (('seq _ ())
     (case reason
       ((none) ctx)
       ((tail) (gen-return (gen-push-unspecified ctx)))
       ((push) (gen-push-unspecified ctx))))
    (('seq _ (? list? children))
     (let ((rec-comp (case reason
                       ((none) comp-node)
                       ((tail) comp-tail)
                       ((push) comp-push))))
       (let lp ((lst children) (ctx ctx))
         (if (null? (cdr lst))
             (rec-comp (car lst) ctx)
             (lp (cdr lst) (comp-node (car lst) ctx))))))))

(define (build-closure label-entry vars ctx)
  (define (build vars ctx)
    (if (null? vars)
        (gen-push-constant '() ctx)
        (gen-prim 'cons
                  2
                  #f
                  (build (cdr vars)
                         (gen-push-local-var (car vars) ctx)))))
  (display "ZZZZ")(display (->list (caddr (->list ctx))))(newline)
  (if (null? vars)
      (gen-closure label-entry
                   (gen-push-constant '() ctx))
      (gen-closure label-entry
                   (build vars ctx))))

(define (comp-prc node closure? ctx)
  (let*-values
      (((ctx2 label-entry) (context-make-label ctx))
       ((ctx3 label-continue) (context-make-label ctx2))
       ((body-env) (prc->env node))
       ((ctx4)
        (if closure?
            (begin         (format #t "node: ~a~%"  (node->expr node))

            (build-closure label-entry (env-closed body-env) ctx3))
            ctx3))
       ((ctx5) (gen-goto label-continue ctx4))
       ((ctx6) (gen-entry (length (prc-params node))
                          (prc-rest? node)
                          (context-add-bb
                           (context-change-env ctx5
                                               body-env)
                           label-entry)))
       ((ctx7) (comp-tail (child1 node) ctx6)))
    (prc-entry-label-set! node label-entry)
    (context-add-bb (context-change-env ctx7 (context-env ctx5))
                    label-continue)))

(define (prc->env prc)
  (make-env
   (let ((params (prc-params prc)))
     (make-stk (length params) (map var-bare-id params)))
   (map var-bare-id (non-global-fv prc))))

(define (comp-call node reason orig-ctx)
  (cond
   ((call? node)
    (let* ((op (car (node-children node)))
           (args (cdr (node-children node)))
           (nargs (length args))
           (ctx (fold (lambda (arg ctx) (comp-push arg ctx))
                      orig-ctx args))) ; push all the arguments
      ;; generate the call itself
       (match (->list op)
         (('ref _ () (? var-primitive var)) ; primitive call
          (let* ((id (var-bare-id var))
                 (primitive (var-primitive var))
                 (prim-nargs (primitive-nargs primitive))
                 (result-ctx
                  (if (not (= nargs prim-nargs))
                      (compiler-error
                       "comp-call: primitive called with wrong number of arguments" id)
                      (gen-prim id prim-nargs
                                (primitive-unspecified-result? primitive)
                                ctx)))
                 (unspecified? (primitive-unspecified-result? primitive))
                 (result (if unspecified?
                             (gen-push-unspecified result-ctx)
                             result-ctx)))
            (case reason
              ((tail) (gen-return result))
              ((push) result)
              (else (if unspecified?
                        result-ctx
                        (gen-pop result-ctx))))))
         (('ref _ () var)
          (=> unmatch)
          (cond 
           ((needs-closure? var)
            =>
            (lambda (prc)
              (case reason
                ((tail) (gen-jump-toplevel nargs prc ctx))
                ((push) (gen-call-toplevel nargs prc ctx))
                (else (gen-pop (gen-call-toplevel nargs prc ctx))))))
           (else (unmatch))))
         (_
          (let ((ctx2 (comp-push op ctx)))
            (case reason
              ((tail) (gen-jump nargs ctx2))
              ((push) (gen-call nargs ctx2))
              (else (gen-pop (gen-call nargs ctx2)))))))))
       (else (compiler-error "comp-call: Invalid call site node!" node))))
  
(define (comp-test node label-true label-false ctx)
  (match (->list node)
    (('cst _ () val)
     (let ((ctx2 (gen-goto (if val label-true label-false) ctx)))
       (context-change-env2 ctx2 (context-env ctx2))))
    ((or (? %ref?) (? %def?) (? %set?) (? %if*?)
          (? %call?) (? %seq?))
     (let* ((ctx2 (comp-push node ctx))
            (ctx3 (gen-goto-if-false label-false label-true ctx2)))
       (context-change-env2 ctx3 (context-env ctx3))))
    ((? %prc?) ; always true
     (let ((ctx2 (gen-goto label-true ctx)))
       (context-change-env2 ctx2 (context-env ctx2))))
    (else (compiler-error "comp-test: unknown expression type" node))))
