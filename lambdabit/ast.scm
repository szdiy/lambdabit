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

(define-module (lambdabit ast)
  #:use-module (srfi srfi-1)
  #:use-module (ice-9 match)
  #:use-module ((rnrs) #:select (define-record-type))
  #:use-module (lambdabit env)
  #:use-module (lambdabit utils))

(module-export-all! (current-module))

;; Syntax-tree node representation.

;; The AST is doubly linked, children point to their parent. This makes it
;; possible to crawl the tree backwards, which is useful for some analysis
;; and transformations.

;; In addition, variable objects are doubly linked as well. Defs, refs, sets
;; and prcs point to the variables involved, and the variables point back to
;; their definition, references and assignments. Again, this makes analysis
;; and transformations easier.

;; Important invariant: No node sharing.
;; If we create identical nodes, or copy an existing node, the results
;; must _not_ be eq?.
;; Otherwise, this may screw up accounting (e.g. for refs) or cycle
;; detection in analysis, etc.

(define-record-type node (fields (mutable parent) (mutable children)))

(define (child1 node) (car (node-children node)))

(define (immutable-var? var) (null? (var-sets var)))
(define (mutable-var? var) (not (immutable-var? var)))

;; If v is defined, return the node corresponding to its value.
;; Returns #f if something goes wrong.
(define (var-val v)
  (define def (var-def v))
  (and (immutable-var? v)
       def
       (not (prc? def)) ; var defined in a lambda, no fixed value
       (child1 def)))   ; rhs of a define

(define-record-type cst (parent node) (fields val))
(define-record-type ref (parent node) (fields var))
(define-record-type def (parent node) (fields var)) ; children: (rhs)
(define-record-type set (parent node) (fields var)) ; children: (rhs)
(define-record-type if* (parent node))    ; children: (test then else)
(define-record-type prc 
  (parent node)        ; children: (body)
  (fields (mutable params) rest? (mutable entry-label)))
(define-record-type call (parent node))   ; children: (op . args)
(define-record-type seq (parent node))   ; children: (body ...)

;; parsing helpers
(define (extract-ids pattern) pattern) ; now we just return the list as ids
;; '(a b . c) is not-list, but '(a b c) is list
;; FIXME: so ugly
(define (has-rest-param? pattern) (not (list? pattern))) 

;; AST construction helpers

(define (create-ref v)
  (define r (make-ref #f '() v)) ; parent needs to be set by caller
  (var-refs! v (cons r (var-refs v)))
  r)
;; Needs to be called every time we remove a ref from the AST to avoid
;; dangling references which hurt analysis precision.
(define (discard-ref r)
  (define var  (ref-var r))
  (define refs (var-refs var))
  (unless (memq r refs)
    (compiler-error "discard-ref: ref is not in the variable's refs"
                    (var-id var)))
  (var-refs! var (remq r refs)))
(define (discard-set s)
  (define var  (ref-var s))
  (define sets (var-sets var))
  (unless (memq s sets)
    (compiler-error "discard-set: set is not in the variable's sets"
                    (var-id var)))
  (var-sets! var (remq s sets)))

;; Crawls e and discards any refs, and sets it encounters, so that e can
;; be dropped without leaving dangling references.
(define (discard-node! e parent)
  (define cs (node-children e))
  (when (memq e (node-children (node-parent e)))
    (error "discard-node!: can't discard a node that's still attached"
           (node->expr e)))
  (node-parent-set! e #f)
  (when (ref? e) (discard-ref e))
  (when (set? e) (discard-set e))
  (node-children-set! e '()) ; detach children, so they can be discarded too
  (for-each (lambda (c) (discard-node! c e)) cs))

(define (create-prc children params rest?)
  (make-prc #f children params rest?
            #f)) ; entry-label, will be filled later

(define (fix-children-parent! p)
  (for-each (lambda (x) (node-parent-set! x p)) (node-children p)))

;; Note: if new is a descendant of old, it needs to be copied before begin
;; substituted in. This is because we discard old and all its descendants.
(define (substitute-child! parent old new)
  (define children (node-children parent))
  (unless (memq old children)
    (compiler-error "substitute-child!: old is not in children"
                    (node->expr old)))
  (node-parent-set! new parent)
  (node-children-set! parent (map (lambda (x) (if (eq? x old) new x))
                                  children))
  (discard-node! old parent))

;; Is c a descendant of p?
(define (inside? c p)
  (or (eq? c p)
      (and c ; not at the top of the program
           (inside? (node-parent c) p))))

;; Splice the child begin inside the parent begin in place of the old node.
(define (splice-begin! old child parent)
  (node-children-set!
   parent
   (apply append
          (fold (lambda (c p)
                  (if (eq? c old)
                      (cons (node-children child) p) ; replace it
                      (cons (list c) p))) ; keep it
                '() (node-children parent)))
  (fix-children-parent! parent)))

;; Since nodes know their parents, we can't just reuse them directly.
;; For this reason, this is a deep copy.
;; Optionally takes a list of variable substitutions. When we copy lambdas,
;; we need to create new var objects, otherwise the copy's variables will be
;; the same as the original's.
(define* (copy-node e #:optional (substs '())) ; substs : (listof (pair var var))
  (define (maybe-substitute-var var)
    (cond 
     ((any (lambda (x) (var=? var x)) substs) => cdr)
     (else var)))
  (define new
    (match e
      ;; parent is left #f, caller must set it
      ;; children are copied below
      (('cst _ _ val) ; no need to copy val
       (make-cst #f '() val))
      (('ref _ _ var) ; we may need to substitute
       (create-ref (maybe-substitute-var var))) ; registers the reference
      (('def _ _ var) ; only at the top-level, makes no sense to copy
       (compiler-error "copying the definition of" (var-id var)))
      (('set _ _ var) ; as above
       (make-set #f '() (maybe-substitute-var var)))
      (('if* _ _)
       (make-if* #f '()))
      (('prc _ _ params rest? entry)
       (define new (make-prc #f '() '() rest? entry))
       ;; we need to create new parameters, and replace the old ones in body
       ;; Note: with Racket identifiers being used for variables, we'll need
       ;; to freshen the new vars, otherwise the new ones will be
       ;; free-identifier=? with the old ones, and we don't want that!
       (define (copy-var v)
         (make-local-var (genid (var-id v)) new))
       (define new-params (map copy-var params))
       (prc-params-set! new new-params)
       new)
      (('call _ _)
       (make-call #f '()))
      (('seq _ _)
       (make-seq #f '()))))
  ;; If we're copying a lambda, we need to substitute the new one's params
  ;; for the original's
  (define new-substs
    (if (prc? new)
        (append (map cons (prc-params e) (prc-params new))
                substs)
        substs))
  (node-children-set! new 
                      (map (lambda (c) (copy-node c new-substs)) (node-children e)))
  (fix-children-parent! new)
  new)

;; Pretty-printer, mostly for debugging

(define (node->expr node)
  (match node
    (('cst _ '() val)
     (if (self-eval? val)
         val
         (list 'quote val)))
    (('ref _ '() var)
     (var-bare-id var))
    (('def _ `(,rhs) var)
     (list 'define (var-bare-id var) (node->expr rhs)))
    (('set _ `(,rhs) var)
     (list 'set!   (var-bare-id var) (node->expr rhs)))
    (('if* _ `(,tst ,thn ,els))
     (list 'if (node->expr tst) (node->expr thn) (node->expr els)))
    (('prc _ `(,body) params rest? _)
     (define (build-pattern params rest?)
       (cond 
        ((null? params) '())
        ((null? (cdr params))
         (if rest?
             (var-bare-id (car params))
             (list (var-bare-id (car params)))))
        (else
         (cons (var-bare-id (car params))
               (build-pattern (cdr params) rest?)))))
     `(lambda ,(build-pattern params rest?)
        ,(node->expr body)))
    (('call _ children) (map node->expr children))
    (('seq _ children) (cons 'begin (map node->expr children)))
    (else (compiler-error "unknown expression type" node))))
