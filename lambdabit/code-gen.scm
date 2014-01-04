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

(define-module (lambdabit code-gen)
  #:use-module (ice-9 format)
  #:use-module (lambdabit ir)
  #:export (gen-instruction
            gen-entry 
            gen-push-constant
            gen-push-unspecified
            gen-push-local-var
            gen-push-stack
            gen-push-global
            gen-set-global
            gen-call
            gen-jump
            gen-call-toplevel
            gen-jump-toplevel
            gen-goto
            gen-goto-if-false
            gen-closure
            gen-prim
            gen-pop
            gen-return))
(define ->list (@ (lambdabit utils) ->list))

;; Code generation utility.
;; Each of these adds an IR instruction to the code stream.

(define (gen-instruction instr nb-pop nb-push ctx)
  ;;(format #t "GEN-INSTR: ~a,~a,~a,~a~%" instr nb-pop nb-push ((@ (lambdabit utils) ->list) ctx))
  (let* ((env (context-env ctx))
         (stk (stack-extend #f
                            nb-push
                            (stack-discard nb-pop (env-local env)))))
    (context-add-instr (context-change-env ctx (env-change-local env stk))
                       instr)))

;; function entry
(define (gen-entry nparams rest? ctx)
  (gen-instruction `(entry ,nparams ,rest?) 0 0 ctx))

;; push constant to function stack
(define (gen-push-constant val ctx)
  (gen-instruction `(push-constant ,val) 0 1 ctx))

(define (gen-push-unspecified ctx)
  (gen-push-constant #f ctx))
(use-modules (ice-9 match))
;; push local vars to function stack
(define (gen-push-local-var var ctx)
  (let ((i (find-local-var var (context-env ctx))))
    (format #t "ABCD: ~a~% ~{~a~^  ||  ~a~}, ==> ~a~%" var (match (context-env ctx) (($ env _ local closed) (cons (->list local) closed))) i)
    (if (>= i 0)
        (gen-push-stack i ctx)
        (gen-push-stack ; in the closed env, past the local variables
         (+ (- -1 i)
            (length (stk-slots (env-local (context-env ctx))))) ctx))))

(define (gen-push-stack pos ctx)
  (gen-instruction `(push-stack ,pos) 0 1 ctx))

(define (gen-push-global var ctx)
  (gen-instruction `(push-global ,var) 0 1 ctx))

(define (gen-set-global var ctx)
  (gen-instruction `(set-global ,var) 1 0 ctx))

;; function call
(define (gen-call nargs ctx)
  (gen-instruction `(call ,nargs) (+ nargs 1) 1 ctx))

;; jump code
(define (gen-jump nargs ctx)
  (gen-instruction `(jump ,nargs) (+ nargs 1) 1 ctx))

;; call from top-level
(define (gen-call-toplevel nargs id ctx)
  (gen-instruction `(call-toplevel ,id) nargs 1 ctx))

(define (gen-jump-toplevel nargs id ctx)
  (gen-instruction `(jump-toplevel ,id) nargs 1 ctx))

(define (gen-goto label ctx)
  (gen-instruction `(goto ,label) 0 0 ctx))

(define (gen-goto-if-false label-false label-true ctx)
  (gen-instruction `(goto-if-false ,label-false ,label-true) 1 0 ctx))

(define (gen-closure label-entry ctx)
  (gen-instruction `(closure ,label-entry) 1 1 ctx))

(define (gen-prim id nargs unspec-result? ctx)
  (gen-instruction `(prim ,id)
                   nargs
                   (if unspec-result? 0 1)
                   ctx))

(define (gen-pop ctx)
  (gen-instruction '(pop) 1 0 ctx))

(define (gen-return ctx)
  (let ((ss (stk-size (env-local (context-env ctx)))))
    (gen-instruction '(return) ss 0 ctx)))
