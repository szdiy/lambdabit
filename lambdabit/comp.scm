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

(define (comp-node n ctx)
  (begin (display "VVVVVV00")(display (->list (cadr (->list (caddr (->list ctx))))))(newline))
  (match (->list n)
    ((or (? %cst?) (? %ref?) (? %prc?))
     ctx) ; we can drop any of these if we don't care about their value
    (('def _ (rhs) var)
     (if (needs-closure? var)
         (begin
           (format #t "YES: ~a~%" (->list rhs))
           (comp-prc rhs #f ctx))
         (if (var-needed? var)
             (let ((ctx2 (comp-push rhs ctx)))
               (display "YES2\n")
               (gen-set-global (var-bare-id var) ctx2))
             (comp-node rhs ctx))))
    (('set _ (rhs) var)
     (if (var-needed? var)
         (let ((ctx2 (comp-push rhs ctx)))
           (gen-set-global (var-bare-id var) ctx2))
         (comp-node rhs ctx)))
    ((? %if*?)
     (comp-if n 'none ctx))
    ((? %call?)
     (comp-call n 'none ctx))
    ((? %seq?)
     (comp-seq n 'none ctx))
    (else (compiler-error "comp-node: unknown expression type" n))))

(define (comp-tail n ctx)
  (match (->list n)
    ((or (? %cst?) (? %ref?) (? %def?) (? %set?) (? %prc?))
     (gen-return (comp-push n ctx)))
    ((? %if*?)
     (comp-if n 'tail ctx))
    ((? %call?)
     (comp-call n 'tail ctx))
    ((? %seq?)
     (comp-seq n 'tail ctx))
    (else (compiler-error "comp-tail: unknown expression type" n))))

(define (comp-push n ctx)
  (match (->list n)
    (('cst _ () val)
     (gen-push-constant val ctx))
    (('ref _ () var)
     (format #t "comp-push: ~a~%" (->list var))
     (cond 
      ((not (var-global? var)) ; not a global var, get from local
       (gen-push-local-var (var-bare-id var) ctx))
      ((var-def var) ; var was defined
       (let ((val (var-val var))) ; non-false implies immutable
         (if (cst? val) ; immutable global, counted as cst
             (gen-push-constant (cst-val val) ctx)
             (gen-push-global (var-bare-id var) ctx))))
      (else (compiler-error "comp-push: undefined variable:" (var-id var)))))
    ((or (? %def?) (? %set?))
     (gen-push-unspecified (comp-node n ctx)))
    ((? %if*?)
     (comp-if n 'push ctx))
    ((? %prc?)
     (comp-prc n #t ctx))
    ((? %call?)
     (comp-call n 'push ctx))
    ((? %seq?)
     (comp-seq n 'push ctx))
    (else (compiler-error "comp-push: unknown expression type" n))))

(define (comp-if n reason ctx)
  (match (->list n)
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

(define (comp-seq n reason ctx)
  (match (->list n)
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
        (gen-prim 'cons 2 #f
                  (build (cdr vars)
                         (gen-push-local-var (car vars) ctx)))))
  (if (null? vars)
      (gen-closure label-entry
                   (gen-push-constant '() ctx))
      (gen-closure label-entry
                   (build vars ctx))))

(define (comp-prc n closure? ctx)
  (format #t "YYYYY: ~a~%" (node->expr n))
  ;;(format #t "closure? ~a~%" closure?)
  (let*-values
      (((ctx2 label-entry) (context-make-label ctx))
       ;;((ccc) (begin (display "ZZZZ11")(display (->list (env-local (context-env ctx2))))(newline)))
       ((ctx3 label-continue) (context-make-label ctx2))
       ;;((ccc) (begin (display "ZZZZ22")(display (->list (env-local (context-env ctx3))))(newline)))
       ((body-env) (prc->env n))
       ;;((ccc) (format #t "HMM: ~a~%~a~%" (->list body-env) (env-closed body-env)))
       ((ctx4)
        (if closure?
            (build-closure label-entry (env-closed body-env) ctx3)
            ctx3))
       ;;((ccc) (begin (display "ZZZZ33")(display (->list (env-local (context-env ctx4))))(newline)))
       ((ctx5) (gen-goto label-continue ctx4))
       ;;((ccc) (begin (display "ZZZZ44")(display (->list (env-local (context-env ctx5))))(newline)))
       ((ctx6) (gen-entry (length (prc-params n))
                          (prc-rest? n)
                          (context-add-bb
                           (context-change-env ctx5
                                               body-env)
                           label-entry)))
       ((ctx7) (comp-tail (child1 n) ctx6)))
    (prc-entry-label-set! n label-entry)
    (context-add-bb (context-change-env ctx7 (context-env ctx5))
                    label-continue)))

(define (prc->env prc)
  ;;  (format #t "MMMMMMM: ~a~%" (node->expr prc))
  (make-env
   (let ((params (prc-params prc)))
     (format #t "prc->env: ~a, ~a~%" (length params) params)
     (make-stk (length params) (map var-bare-id params)))
   (begin
     (format #t "prc->env: ngf ~a~%" (non-global-fv prc))
     (map var-bare-id (non-global-fv prc)))))

(define (comp-call n reason orig-ctx)
  (cond
   ((call? n)
    (let* ((op (car (node-children n)))
           (args (cdr (node-children n)))
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
       (else (compiler-error "comp-call: Invalid call site node!" n))))

(define (comp-test n label-true label-false ctx)
  (match (->list n)
    (('cst _ () val)
     (let ((ctx2 (gen-goto (if val label-true label-false) ctx)))
       (context-change-env2 ctx2 (context-env ctx2))))
    ((or (? %ref?) (? %def?) (? %set?) (? %if*?) (? %call?) (? %seq?))
     (let* ((ctx2 (comp-push n ctx))
            (ctx3 (gen-goto-if-false label-false label-true ctx2)))
       (context-change-env2 ctx3 (context-env ctx3))))
    ((? %prc?) ; always true
     (let ((ctx2 (gen-goto label-true ctx)))
       (context-change-env2 ctx2 (context-env ctx2))))
    (else (compiler-error "comp-test: unknown expression type" n))))
