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

(define-module (lambdabit front-end)
  #:use-module (srfi srfi-1)
  #:use-module (ice-9 match)
  #:use-module (lambdabit utils)
  #:use-module (lambdabit ast)
  #:use-module (lambdabit env)
  #:use-module (lambdabit analysis)
  #:export (adjust-unmutable-references! inline-calls-to-calls!
            inline-left-left-lambda! constant-fold! copy-propagate!))

;; Front-end code transformations.

;; Note: All optimizations should be careful not to increase code size.

;;-----------------------------------------------------------------------------

(define (adjust-unmutable-references! node)
  (match node
    (('call parent (('ref _ () var)
                    (and child ('ref _ () (? immutable-var? v)))))
     (=> fail!)
     (cond 
      ((var=? var (env-lookup global-env '%unbox))
       (substitute-child! parent node (copy-node child))
       child)
      (else (fail!))))
    (else
     (for-each adjust-unmutable-references! (node-children node))
     node)))

;;-----------------------------------------------------------------------------

;; Beta reduction. Side-effectful. Returns the new node if succeeds, else #f.
(define (beta! e)
  (match e
    (('call parent (op . args))
     (=> fail!)
     (let* ((proc
             (match op
               (('ref _ _ (? immutable-var? (app var-val proc)))
                ;; ref to an immutable var bound to a lambda, we're generous
                proc)
               ((? %prc? proc)
                proc)
               (else (fail!))))
            ;; We copy the entire proc to make sure that the body always has a parent.
            ;; Otherwise, substitution may error. Of course, only the body ends up in
            ;; the actual program.
            (new-proc (copy-node proc)))
       (match new-proc
         (('prc _ (body) params #f _) ; no rest arg
          (unless (= (length params) (length args))
            (fail!))
          ;; Bottom-up beta reduction, this is due to Shivers and Wand.
          ;; For each variable we need to substitute, we iterate over its refs,
          ;; and substitute directly from there, without having to traverse the
          ;; whole term.
          (reset
           (let ((o (either params)) (n (either args)))
             (for-each 
              (lambda (r)
                (and (inside? r body)
                     ;; Since we just copied the lambda, we're guaranteed that all
                     ;; the refs will be in its body.
                     (substitute-child! (node-parent r) r (copy-node n))))
              (var-refs o))))
          ;; Hook the new body up. We need to get it from new-proc, since the
          ;; original body may have been substituted away.
          (let ((new (child1 new-proc)))
            (cond ((and (seq? parent) (seq? new)) ; splice the new begin in the old
                 (splice-begin! e new parent)
                 (fix-children-parent! parent))
                  (else ; just replace the original child
                 ;; This discards e, which includes the lambda (if left-left-
                 ;; lambda) and the args. This shouldn't leave leftover nodes.
                   (substitute-child! parent e (copy-node new))))
            ;; We return the new node.
            ;; Note: new may not actually be in the program. It may have been
            ;; spliced away in its parent.
            ;; So far, all we do with the return value of beta! is to recur on it,
            ;; which basically means exploring its children. In the splicing case,
            ;; the children will have new's parent (not new itself) as parent, so
            ;; traversing them should do the right thing. (Replacing them in place
            ;; will change new's parent's children, as it should.)
            new)))))
     (else #f))) ; invalid beta, do nothing

;;-----------------------------------------------------------------------------

;; When an operator is a reference to a function whose body is just a call, we
;; may be able to inline without increasing code size.
;; All args to the inner call need to be trivial (cst or ref), and there needs
;; to be at most as many as there are arguments in the original call.
;; ex: (define (foo x y) (bar x y)) (foo 1)
;;     => (bar 1)
;; Optionally takes a list of vars seen for a given call site.
;; Every time we successfully change the operator, we add it to the list.
;; If we see something again, we're looping, so stop there.
(define* (inline-calls-to-calls! node #:optional (seen '()))
  (match node
    (('call _ ((ref _ () (and orig-var (app var-val val))) . args))
     (=> fail!)
     (match val
       (('prc _ (body) _ #f _)
        (match body
          (('call _ ((ref _ () inside-var) . inside-args))
           ;; We need to be careful to not increase code size.
           (if (and (<= (length inside-args) (length args)) ; not too many
                    (every (lambda (i-a)
                             (and (or (ref? i-a) (cst? i-a)) ; not too big
                                  (side-effect-oblivious? i-a))) ; can be moved
                           inside-args)
                    ;; Don't loop.
                    (not (any (lambda (s) (and (var=? s inside-var) s)) seen)))
               (let ((new (beta! node)))
                 ;; If beta fails, nothing was changed. No point in recurring,
                 ;; since trying again is useless, and all our children are
                 ;; trivial (cst or ref).
                 ;; If beta succeeds, we recur, there may be new opportunities.
                 ;; Note: new may not be a node that's actually in the program.
                 ;; See comment in beta!.
                 (when new (inline-calls-to-calls! new (cons orig-var seen))))
               (fail!)))
          (else (fail!))))
       (else (fail!))))
    (else (for-each inline-calls-to-calls! (node-children node)))))

;;-----------------------------------------------------------------------------

;; If it would not cause a code size increase, inline immediately applied
;; lambdas.
;; This should be done after copy propagation, which exposes more of these.
(define (inline-left-left-lambda! node)
  (match node
    (('call _ (('prc _ (body) params #f _) . args))
     (=> fail!)
     (cond 
      ((every (lambda (arg p)
                (or (cst? arg) (ref? arg) ; trivial, won't increase size
                    ;; non-trivial args can be inlined if they're used only once
                    ;; otherwise, may increase code size
                    (and (= (length (var-refs p)) 1)
                         (side-effect-oblivious? arg))))
              args params)
       (let ((new (beta! node)))
         (when new
           (inline-left-left-lambda! new)))) ; maybe there's more
      (else (fail!))))
    (else (for-each inline-left-left-lambda! (node-children node)))))

;;-----------------------------------------------------------------------------

(define (constant-fold! node)
  (match node
    ;; if we're calling a primitive
    (('call p ((ref _ () (? var-primitive op)) . args))
     (=> fail!)
     (for-each constant-fold! args) ; fold args before the whole call
     (let ((folder (primitive-constant-folder (var-primitive op)))
           ;; (we need to access the children again (can't just use `args',
           ;; since constant folding may have mutated them)
           (args (cdr (node-children node))))
       ;; the primitive can do constant-folding, and the args are constant
       ;; folder takes the values of the args, and returns the value of the res
       (cond 
        ((and folder (and-map cst? args))
         ;; if the folding would raise an error, just don't do it, and
         ;; error at runtime
         (catch #t
          (lambda ()
            ;; replace the call with the constant
            (let* ((res-val (apply folder (map cst-val args)))
                   (res (make-cst p '() res-val)))
              (substitute-child! p node res)))
          (lambda e (fail!)))) ; something went wrong, back off
        (else (fail!)))))
    (('if* _ cs) ; if result of test is known, discard unused branch
     (=> fail!) 
     (for-each constant-fold! cs) ; fold each branch
     (match node
       (('if* p ((cst _ () val) thn els))
        (substitute-child! p node (copy-node (if val thn els))))
       (else (fail!))))
    (('seq p cs) ; can discard effect-free non-final elements 
     (=> fail!)
     (for-each constant-fold! cs)
     (let* ((new-cs (node-children node)) ; original cs may have been mutated
            (result (last new-cs))
            (before (remq result new-cs)))
       (if (and-map side-effect-less? before)
           (substitute-child! p node (copy-node result))
           (fail!))))
    (else (for-each constant-fold! (node-children node)))))

;;-----------------------------------------------------------------------------

(define (copy-propagate! expr)
  (match expr
    (('ref p () (and var (? immutable-var? (app var-val (? values val)))))
     (=> fail!)
     (define (replace! new)
       (unless (node-parent expr) (fail!)) ; no parent, stale node, ignore
       (substitute-child! p expr (copy-node new))
       (copy-propagate! p)) ;  there may be more to do, start our parent again
       ;; Single use, copy-propagate away! Can't increase code size.
       ;; Note: due to dangling references, we may be conservative, and
       ;; not notice when something has a single reference.
     (cond 
      ((and (= (length (var-refs var)) 1)
            (side-effect-oblivious? val))
       ;; We need to make sure we're not inlining in ourselves.
       (if (inside? p val)
           (fail!)
           (replace! val)))
      (else ; multiple uses, but maybe we can do it anyway
       (match val
         ((or ('ref _ () _) ('cst _ () _))
          ;; constants are ok. even if they're large, they're just a
          ;; pointer into ROM, where the constant would have been anyway
          ;; (and no duplication)
          (replace! val))
         (else (fail!)))))) ; anything else would increase code size
    (else (for-each copy-propagate! (node-children expr)))))
