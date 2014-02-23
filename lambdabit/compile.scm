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

(define-module (lambdabit compile)
  #:use-module (ice-9 getopt-long)
  #:use-module (ice-9 pretty-print)
  #:use-module (srfi srfi-1)
  #:use-module (lambdabit utils)
  #:use-module (lambdabit back-end)
  #:use-module (lambdabit env)
  #:use-module (lambdabit reader)
  #:use-module (lambdabit parser)
  #:use-module (lambdabit front-end)
  #:use-module (lambdabit ir)
  #:use-module (lambdabit ast)
  #:use-module (lambdabit comp)
  #:use-module (lambdabit back-end)
  #:use-module (lambdabit assembler)
  #:use-module (lambdabit analysis)
  #:use-module (lambdabit sched)
  #:use-module (lambdabit tree-shaker)
  #:export (compile))

(define usage 
  "Usage: compile [options]* filename
 
   -h | --help         ==> Show this screen.
   -s | --size         ==> Display the size of the generated bytecode.
   -p | --parse        ==> Display post-parsing representation of the program.
   -f | --front        ==> Display post-front-end representation of the program.
   -S | --asm          ==> Display generated bytecode pre-assembly.
   -t | --status       ==> Display statistics about generated instructions.
   -o | --output       ==> Place the output into the given file.

 Written with GNU Guile by NalaGinrut<nalaginrut@gmail.com> (C)2013,2014.
 ")
 
(define option-spec
  '((help (single-char #\h) (value #f))
    (size (single-char #\s) (value #f))
    (parse (single-char #\p) (value #f))
    (parse (single-char #\p) (value #f))
    (front (single-char #\f) (value #f))
    (asm (single-char #\S) (value #f))
    (status (single-char #\t) (value #f))
    (output (single-char #\o) (value #t))))

(define (outfile-gen file)
  (define (gen-file file)
    (let ((ext (get-file-ext file)))
      (if (string=? ext "hex")
          file
          (string-append file ".hex"))))
  (let ((hex-filename (gen-file file)))
    (and (file-exists? hex-filename)
         (delete-file hex-filename))
    hex-filename))

(define (get-the-opts args) 
  (let ((len (length args)))
    (cond
     ((< len 1)
      (display usage)
      (primitive-exit 0))
     (else
      (cons "place-holder" ; getopt-long needs the first elem as the place-holder
            (list-head args (1- len)))))))

(define (get-the-file args) 
  (if (< (length args) 1) 
      (begin (display usage) (exit 1))
      (last args)))

(define (compile . args)
  (define filename (get-the-file args))
  (define options (getopt-long (get-the-opts args) option-spec))
  (display args)(newline)
  (parameterize
    ((need-help (option-ref options 'help #f))
     (show-size (option-ref options 'size #f))
     (show-parsed (option-ref options 'parse #f))
     (show-front (option-ref options 'front #f))
     (print-asm (option-ref options 'asm #f))
     (show-status (option-ref options 'status #f))
     (outfile (option-ref options 'output #f)))
    ;;(format #t "~a~%" args)
    ;;(format #t "~a,~a,~a,~a,~a,~a,~a~%" (need-help) (show-size) (show-parsed) (show-front) (print-asm) (show-front) (outfile))
    ;;(format #t "~a~%" filename)
    (cond
     ((need-help) 
      (display usage)
      (primitive-exit)) ;; show help and exit.
     ((string=? filename "-")
      (do-compile (current-input-port) (current-output-port)))
     (else 
      (do-compile (open-input-file filename)
                  (open-output-file (outfile-gen (if (outfile) (outfile) (default-outfile)))))))))

(define *optimization-passes*
  (list
   adjust-unmutable-references! ; done first to expose more left-left-lambdas, help constant folding, etc.
   copy-propagate!
   inline-left-left-lambda! ; gives constant folding more to do
   inline-calls-to-calls!   ; same
   copy-propagate!          ; same
   constant-fold!
   copy-propagate!          ; again, for cleanup
   ;; analysis needed by the back-end
   mark-needed-global-vars!))

(define (do-compile-optimization! node)
  (for-each (lambda (p) (display p) (newline)(p node)) *optimization-passes*))

(define (do-compile in-port out-port)
  (let* ((forms (read-program in-port))
         (node (parse-program forms global-env)))
    (when (show-parsed)
      (pretty-print (node->expr node)))
    (do-compile-optimization! node)
    (when (show-front)
      (pretty-print (node->expr node)))
    (display "############# done2\n")
    (let* ((ctx  (begin (display "2.1\n")(comp-node node (make-init-context))))
           (code (begin (display "2.2\n")(context-code ctx)))
           (bbs  (begin (display "2.3\n")(code->vector code))))
      (display "########## done3\n")
      (resolve-toplevel-labels! bbs)
      (display "########## done4\n")
      (let ((prog (schedule (tree-shake! bbs))))
      (display "########## done5\n")

        (when (print-asm)
          (pretty-print prog))
        ;; output port is in a thunk to avoid creating result
        ;; files if compilation fails
        (let ((size (assemble prog out-port)))
          (display "########## done6\n")
          (when (show-size)
            (format #t "~a bytes\n" size)))))))
