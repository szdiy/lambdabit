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

(define-module (lambdabit reader)
  #:use-module (srfi srfi-4)
  #:use-module (ice-9 match)
  #:use-module (lambdabit utils)
  #:export (read-program))

(define-syntax-rule (->lib file)
  (format #f "~a/~a" (current-libpath) file))

(define (expand-include expr)
  (match expr
    ((include file)
     (when (not (file-exists? file))
       (error expand-include "No such file to include" file))
     (let ((in (open-input-file file)))
       (get-all-exprs-from-port in)))
    (else expr)))

(define (get-all-exprs-from-port port)
  (let lp((expr (read port)) (ret '()))
    (cond
     ((eof-object? expr) (reverse ret))
     (else
      (let ((e (expand-include expr)))
        (lp (read port) (cons e ret)))))))

(define (read-program port)
  ;; we have to put read-lib and the-library in read-program to make sure that
  ;; libs was refreshed in each time compiling.
  (define (read-lib f)
    (if (file-exists? f)
        (call-with-input-file f get-all-exprs-from-port)
        (error read-program "The file doesn't exist!" f)))
  (define the-library
    `(,@(read-lib (->lib "library.scm"))        ; architecture-independent
      ,@(read-lib (->lib "arch-library.scm")))) ; architecture-dependent 
  `(,@the-library ,@(get-all-exprs-from-port port)))
