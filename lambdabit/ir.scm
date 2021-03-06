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

(define-module (lambdabit ir)
  #:use-module (lambdabit utils)
  #:use-module (lambdabit ast)
  #:use-module (lambdabit env)
  #:use-module (ice-9 q)
  #:use-module (ice-9 match)
  #:use-module ((rnrs) #:select (define-record-type))
  #:use-module (srfi srfi-1))

(module-export-all! (current-module))

(define-record-type context (fields code env env2))

(define (context-change-code ctx code)
  (make-context code
                (context-env ctx)
                (context-env2 ctx)))

(define (context-change-env ctx env)
  (make-context (context-code ctx)
                env
                (context-env2 ctx)))

(define (context-change-env2 ctx env2)
  (make-context (context-code ctx)
                (context-env ctx)
                env2))

(define (make-init-context)
  (make-context (make-init-code)
                (make-init-env)
                #f))

(define (context-make-label ctx)
  (let ((r (context-change-code ctx (code-make-label (context-code ctx)))))
    (values r (code-last-label (context-code r)))))

(define (context-add-bb ctx label)
  (context-change-code ctx (code-add-bb (context-code ctx) label)))

(define (context-add-instr ctx instr)
  (context-change-code ctx (code-add-instr (context-code ctx) instr)))

;; Representation of code.

(define-record-type code (fields last-label rev-bbs))
(define-record-type bb (fields label (mutable rev-instrs)))

(define (make-init-code)
  (make-code 0
             (list (make-bb 0 (list)))))

(define (code-make-label code)
  (make-code (+ (code-last-label code) 1)
             (code-rev-bbs code)))

(define (code-add-bb code label)
  (make-code (code-last-label code)
             (cons (make-bb label '())
                   (code-rev-bbs code))))

(define (code-add-instr cur-code instr)
  (match (->list cur-code)
    (('code last-label (($ bb _ label rev-instrs) . rest))
     (make-code last-label
                (cons (make-bb label
                               (cons instr rev-instrs))
                      rest)))))

;; Representation of compile-time stack.
;; NOTE: this stack implementation has no side-effect

;;; A stack is a (make-stack size slots) where:
;;; - size is the number of slots
;;; - slots is a list of variables or #f in each slot
;; NOTE: This stack implementation is non-side-effect, so it's called 'safe'.
;; non-side-effect is important here, because we don't have to save/restore the stack
;; explicitly, maybe less efficient, but convinient.
(define-record-type stk (fields size slots))

(define (make-init-stack)
  (make-stk 0 '()))

(define (stack-extend x nb-slots stack)
  (match stack
    (($ stk _ size slots)
     (make-stk (+ size nb-slots) (append (make-list nb-slots x) slots)))
    (else (error stack-extend "wrong stack type!" stack))))

(define (stack-discard nb-slots stack)
  ;;(format #t "STK-DISCARD: ~a, ~a~%" nb-slots (->list stack))
  (match stack
    (($ stk _ size slots)
     (make-stk (- size nb-slots) (list-tail slots nb-slots)))
    (else (error stack-discard "wrong stack type!" stack))))

;; (define* (make-stk #:optional (lst #f)) ; NOTE: make-stack exists in Guile
;;   (let ((stk (make-q)))
;;     (and lst (for-each (lambda (x) (enq! stk x)) lst))
;;     stk))
;; (define stack-slots car)
;; (define stack-size q-length)
;; (define stack-pop! q-pop!)
;; (define stack-push! q-push!)
;; (define stack-empty? q-empty?)

;; (define (make-init-stack)
;;   (make-stk))

;; (define (stack-extend x nb-slots stk)
;;   (set-car! stk (append (make-list nb-slots x) (stack-slots stk)))
;;   (sync-q! stk))

;; (define (stack-discard nb-slots stk)
;;   (unless (stack-empty? stk)
;;     (set-car! stk (list-tail (stack-slots stk) nb-slots)))
;;   (sync-q! stk))

;; Representation of compile-time environment.
(define-record-type env (fields local closed))

(define (make-init-env)
  (make-env (make-init-stack) '()))

(define (env-change-local env local)
  (make-env local (env-closed env)))

(define (env-change-closed env closed)
  (make-env (env-local env) closed))

(define (find-local-var var env)
  (define target? (lambda (x) (eq? x var)))
  (format #t "var: ~a~%" var)
  (format #t "find-local-var: ~a, ~a~%" var (->list env))
  (format #t "env-closed==> ~a~%" (env-closed env))
  ;;(if (not (list-index target? (env-closed env))) (error "invalid var" var))
  (let ((x (list-index target? (stk-slots (env-local env))))
        (y (list-index target? (env-closed env))))
    (format #t "<<< local ~a~%" x)
    (format #t "<<< closed ~a~%" y)
    (or x (- (1+ y)))))
        
;;  (or (list-index target? (stk-slots (env-local env)))
;;       (- (+ (list-index target? (env-closed env)) 1))))
      ;;(and=> (list-index target? (env-closed env)) (lambda (x) (- (1+ x))))))
