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

(define-module (lambdabit primitives)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-4)
  #:use-module (lambdabit env)
  #:use-module (lambdabit ast)
  #:use-module (lambdabit utils))

(module-export-all! (current-module))

;;(use-modules (ice-9 match) (srfi srfi-1) (srfi srfi-4) (lambdabit env) (lambdabit ast) (lambdabit utils))
(define primitive-encodings '())

(define (create-eta-expansion prim-var nargs)
  ;; We create AST nodes directly. Looks a lot like the parsing of lambdas.
  (define r       (create-prc '() '() #f)) ; children params rest?
  (define ids     (build-list nargs (lambda (x) (genid))))
  (define new-env (env-extend global-env ids r))
  (define args    (map (lambda (id) (env-lookup new-env id)) ids))
  (define op      (create-ref prim-var))
  (define call    (make-call #f (cons op (map create-ref args))))
  (fix-children-parent! call)
  (prc-params-set!    r args)
  (node-children-set! r (list call))
  ;; hidden. you need to know it to get it
  (let* ((eta-id  (genid (var-id prim-var)))
         (eta-var (make-global-var eta-id #f))
         (def     (make-def #f (list r) eta-var)))
    (fix-children-parent! def)
    (var-def! eta-var def)
    (add-extra-code def)
    eta-var))

(define* (define-primitive name nargs encoding #:optional (uns-res? #f))
  (let* ((prim (make-primitive nargs #f #f uns-res?))
         (var  (make-primitive-var name prim)))
    ;; eta-expansion, for higher-order uses
    (primitive-eta-expansion! prim (create-eta-expansion var nargs))
    ;; we need to set env directly, since we create the variables ourselves
    (set-global-env! (cons var global-env))
    (set! primitive-encodings 
          (assoc-set! primitive-encodings name encoding))))

;; generate primitives
(define-primitive '%halt 0 0)
(define-primitive 'pair? 1 1)
(define-primitive 'cons 2 2)
(define-primitive 'car 1 3)
(define-primitive 'cdr 1 4)
(define-primitive 'set-car! 2 5 #:unspecified-result)
(define-primitive 'set-cdr! 2 6 #:unspecified-result)
(define-primitive 'null? 1 7)
(define-primitive 'number? 1 8)
(define-primitive '= 2 9)
(define-primitive '%+ 2 10)
(define-primitive '%- 2 11)
(define-primitive '%mul-non-neg 2 12)
(define-primitive '%div-non-neg 2 13)
(define-primitive '%rem-non-neg 2 14)
(define-primitive '< 2 15)
(define-primitive '> 2 16)
(define-primitive 'logior 2 17)
(define-primitive 'logxor 2 18)
(define-primitive 'eq? 2 19)
(define-primitive 'not 1 20)
(define-primitive 'symbol? 1 21)
(define-primitive 'boolean? 1 22)
(define-primitive 'string? 1 23)
(define-primitive 'string->list 1 24)
(define-primitive 'list->string 1 25)
(define-primitive 'u8vector? 1 26)
(define-primitive '%make-u8vector 1 27)
(define-primitive 'u8vector-ref 2 28)
(define-primitive 'u8vector-set! 3 29 #:unspecified-result)
(define-primitive 'u8vector-length 1 30)
(define-primitive 'return 1 31)
(define-primitive 'pop 0 32 #:unspecified-result)
(define-primitive 'get-cont 0 33)
(define-primitive 'graft-to-cont 2 34 #:unspecified-result)
(define-primitive 'return-to-cont 2 35)
(define-primitive '%sleep 1 36 #:unspecified-result)
(define-primitive '%set-led! 1 37 #:unspecified-result)

;; Since constant folding is a compiler-only concept, it doesn't make
;; much sense to add folders to primitives in the VM, where primitives
;; are defined.
;; Instead, we add the constant folders post-facto. This requires that
;; the foldable primitives actually be defined, though. Since folding
;; is used for "essential" primitives, that shouldn't be an issue.

(define (add-constant-folder name folder)
  (let ((prim (var-primitive (env-lookup global-env name))))
    (primitive-constant-folder! prim folder)))

(define folders
  `((number? . ,number?)
    (%+ . ,+)
    (%- . ,-)
    (%mul-non-neg . ,*)
    (%div-non-neg . ,quotient)
    (%rem-non-neg . ,remainder)
    (= . ,=)
    (< . ,<)
    (> . ,>)
    (pair? . ,pair?)
    (car . ,car)
    (cdr . ,cdr)
    (null? . ,null?)
    (eq? . ,eq?)
    (not . ,not)
    (symbol? . ,symbol?)
    (string? . ,string?)
    (string->list . ,string->list)
    (list->string . ,list->string)
    (u8vector-ref . ,u8vector-ref)
    (u8vector? . ,u8vector?)
    (u8vector-length . ,u8vector-length)
    (boolean? . ,boolean?)
    (logior . ,logior)
    (logxor . ,logxor)))

;; add all constant folders
(for-each (lambda (f)
            (let ((name (car f))
                  (folder (cdr f)))
              (add-constant-folder name folder)))
          folders)

;; Some primitives that can be constant-folded away may not be
;; side-effect-oblivious. For instance, car and cdr are side-effect-less?,
;; but they can't always be moved since their behavior depends on the ordering
;; of other side effects.
(define mutable-data-accessors
  (map (lambda (name) (env-lookup global-env name)) 
       '(car cdr u8vector-ref string->list list->string)))
