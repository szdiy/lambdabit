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

(define-module (lambdabit parser)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-1)
  #:use-module (lambdabit utils)
  #:use-module (lambdabit env)
  #:use-module (lambdabit ast)
  #:use-module (lambdabit ir)
  #:use-module (lambdabit analysis)
  );;#:export (parse-program))

(module-export-all! (current-module))

;; NOTE:
;; These ops includes two parts:
;; 1. hasn't implemented;
;; 2. shouldn't appear in certain position.
;; FIXME: find a better way
(define *wrong-op-lst* 
  '(quote quasiquote unquote unquote-splicing lambda if set!
    cond and or case let let* letrec begin do define delay))

(define (is-wrong-op? op)
  (memq op *wrong-op-lst*))

(define (parse-top-list lst env)
  (append-map (lambda (e) (parse-top e env)) lst))

(define (parse-program lst env)
  (let* ((exprs (append extra-code-env
                        (parse-top-list `(,@lst (%halt)) env)))
         (r (make-seq #f exprs)))
    (fix-children-parent! r)
    r))

(define* (parse-define var val env #:optional (forward-references? #t))
  (let ((var2 (env-lookup env var)))
    (parameterize ((allow-forward-references? forward-references?))
      (let* ((val2 (parse 'value val env))
             (r (make-def #f (list val2) var2)))
        ;;(format #t "parse-define: ~a~%" env)
        (fix-children-parent! r)
        (when (var-def var2)
          (compiler-error "parse-define: variable redefinition forbidden" var2))
        (var-def-set! var2 r)
        (list r)))))

;; returns a list of parsed expressions
(define (parse-top expr env)
  (match expr
    ;; As in the reader, this is a hack. The Racket expander will eventually
    ;; take care of begin, define, etc. and spit out core forms.
    (('begin body ...) ; splicing begins
     (parse-top-list body env))
    (('define (var params ...) body ...) ; definitly defined a function
     (parse-define var `(lambda (,@params) ,@body) env))
    (('define var val)
     (parse-define var val env
      ;; If we're not defining a function, forward references are
      ;; invalid.
      (match val
        (('lambda etc ...) #t) ; defining a function
        (else #f)))) ; defining a var 
    (else 
     (list (parse 'value expr env)))))

(define* (parse use expr env #:optional (operator-position? #f))
  ;;(format #t "*** ~a~%" expr)
  (match expr
    ((? self-eval?)
     (make-cst #f '() expr))
    ((? symbol?)
     ;;(display expr)(newline)
     (let* ((v (env-lookup env expr)) 
            ;; v won't be #f anyway, it'll be created at top-level for forward-reference 
            (prim (var-primitive v)) ; if it's a primitive?
            (var (if (and prim (not operator-position?)) ; if not a primitive function
                     ;; We eta-expand any primitive used in a higher-order fashion.
                     (primitive-eta-expansion prim)
                     v))
            (r (create-ref var)))
       (if (not (var-global? var))
           (let* ((unbox (parse 'value '%unbox env))
                  (app (make-call #f (list unbox r))))
             (fix-children-parent! app)
             app)
           r)))
    (('set! lhs rhs)
     (display "hit!\n")
     ;; Again, hack.
     (let ((var (env-lookup env lhs))
           (val (parse 'value rhs env)))
       (when (var-primitive var)
         (compiler-error "parse: cannot mutate primitive" (var-id var)))
       (if (var-global? var)
           (let ((r (make-set #f (list val) var)))
             (fix-children-parent! r)
             (var-sets-set! var (cons r (var-sets var)))
             r) ; assign to top-level
           (let* ((ref (create-ref var))
                  (bs (create-ref (env-lookup env '%box-set!)))
                  (r (make-call #f (list bs ref val))))
             (display (->list r))(newline)
             (fix-children-parent! r)
             (var-sets-set! var (cons r (var-sets var)))
             r)))) ; assign to local reference
    (('quote datum)
     (make-cst #f '() datum))
    (('if tst thn els ...)
     (let* ((a (parse 'test tst env))
            (b (parse use thn env))
            (c (cond
                ((null? els) (make-cst #f '() #f))
                ((null? (cdr els)) (parse use (car els) env))
                (else (compiler-error "parse: redundant expr follow 'els'!"))))
            (r (make-if* #f (list a b c))))
       (fix-children-parent! r)
       r))
    (('cond body ...) ; should eventually be a macro
     (match body 
       ('()
        (parse use '(if #f #f) env))
       (('else rhs ...)
        (parse use `(begin ,@rhs) env))
       (((tst '=> rhs) other-clauses ...)
        (let ((x (genid)))
          (parse use
                 `(let ((,x tst))
                     (if ,x
                         (rhs ,x)
                         (cond ,@other-clauses)))
                 env)))
       (((tst rhs ...) other-clauses ...)
        (parse use
               `(if ,tst
                    (begin ,@rhs)
                    (cond ,@other-clauses))
               env))))
    (('lambda pattern body* ...)
     (let* ((ids (extract-ids pattern))
            ;; children params rest?
            (r (create-prc '() #f (has-rest-param? pattern)))
            (new-env (env-extend env ids r))
            (x (format #t "ee? ~a, ~a~%" (eq? new-env env) (eq? new-env global-env)))
            (body (parse-body body* new-env))
            (mut-vars (fold (lambda (id p)
                              (let ((v (env-lookup new-env id)))
                                (if (mutable-var? v)
                                    (cons v p)
                                    p)))
                            '() ids)))
       ;;(format #t "MUT-VARS: ~a~%" mut-vars)
       ;;(format #t "expr: ~a~%" expr)
       ;;(format #t "new-env: ~a~%" new-env) ;;(map ->list new-env))
       ;;(read-char)
       (cond 
        ((null? mut-vars)
         ;; FIXME: why ids didn't appear in env?
         (prc-params-set! r
                          (map (lambda (id) (env-lookup new-env id))
                               ids))
         (node-children-set! r (list body))
         (fix-children-parent! r)
         r)
        (else
         (let* ((prc (create-prc (list body) mut-vars #f)) ; no rest
                (new-vars (map var-id mut-vars))
                (tmp-env (env-extend new-env new-vars r))
                (app (make-call r (cons prc
                                        (map (lambda (id)
                                               (parse 'value `(%box ,id) tmp-env))
                                             new-vars)))))
           (for-each (lambda (var) (var-def-set! var prc)) mut-vars)
           (fix-children-parent! app)
           (prc-params-set! r
                            (map (lambda (id) (env-lookup tmp-env id))
                                 ids))
           (node-children-set! r (list app))
           (fix-children-parent! prc)
           r)))))
    (('letrec ((ks vs) ...) body ...)
     (parse use
            `(let ((,ks #f))
               (set! ,ks ,vs)
               ,@body)
            env))
    (('begin forms ...)
     ;;(format #t "11: ~a~%" forms)
     (let ((exprs (map (lambda (x) (parse 'value x env)) forms)))
       (cond 
        ((> (length exprs) 1)
         (let ((r (make-seq #f exprs)))
           (fix-children-parent! r)
           r))
        (else (car exprs)))))
    (('let id ((ks vs) ...) body ...) ; named let
     (parse use
            `(letrec ((,id (lambda (,@ks) ,@body)))
                (,id ,@vs))
            env))
    (('let () body ...)
     (parse use `(begin ,@body) env))
    (('let ((ks vs) ...) body ...)
     (parse use `((lambda (,@ks) ,@body) ,@vs) env))
    (('let* () body ...) ; base case for let*
     (parse use `(let () ,@body) env))
    (('let* ((k v) bindings ...) body ...)
     ;;(format #t "k:~a~%v:~a~%bindings:~a~%body:~a~%" k v bindings body)
     (parse use
            (if (null? bindings)
                `(let ((,k ,v)) ,@body)
                `(let ((,k ,v))
                   (let* (,@bindings)
                     ,@body)))
            env))
    (('and)
     (parse use #t env))
    (('and tst)
     (parse use tst env))
    (('and tst rest ...)
     (parse use `(if ,tst (and ,@rest) #f) env))
    (('or) ; base case for or
     (parse use #f env))
    (('or tst)
     (parse use tst env))
    (('or tst rest ...)
     (if (eq? use 'test)
         ;; we don't need to keep the actual result, we only care about
         ;; its "truthiness"
         (parse use `(if ,tst #t (or ,@rest)) env)
         (parse use
                (let ((v (gensym)))
                  `(let ((,v ,tst))
                      (if ,v ,v (or ,@rest))))
                env)))
    ((op args ...)
     (when (is-wrong-op? op)
       (compiler-error "parse: the compiler does not implement the special form" op))
     (let* ((exprs (cons (parse 'value op env 'operator-position)
                         (map (lambda (e) (parse 'value e env)) args)))
            (r (make-call #f exprs)))
       (and (eq? op '-) (format #t "MMR: ~a, ~a~%" exprs (->list r)))
       (fix-children-parent! r)
       r))
    (else (compiler-error "parse: unknown expression" expr))))
  
(define (parse-body exprs env)
  (parse 'value `(begin ,@exprs) env))
