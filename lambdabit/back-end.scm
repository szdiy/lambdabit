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

(define-module (lambdabit back-end)
  #:use-module (lambdabit ir)
  #:use-module (lambdabit ast)
  #:use-module (lambdabit utils)
  #:use-module (ice-9 match)
  #:use-module (ice-9 control)
  #:use-module (srfi srfi-11)
  #:export (renumber-labels code->vector resolve-toplevel-labels!))

;; Back-end utilities.

;;-----------------------------------------------------------------------------

(define (renumber-labels bbs ref-counts n)
  (define (fix instr)
    (define (make-new-label label)
      (bb-label (list-ref bbs label)))
    (match instr
      (`(,(and opcode (or 'closure 'call-toplevel 'jump-toplevel 'goto)) ,arg)
       (list opcode (make-new-label arg)))
      (`(goto-if-false ,a1 ,a2)
       (list 'goto-if-false (make-new-label a1) (make-new-label a2)))
      (else instr)))

  (let ((new-bbs (make-list n)))
    (let-values (((b label) (in-indexed bbs)))
      (for-each
       (lambda (bb ll)
         (when (> (list-ref ref-counts ll) 0)
           (match (->list bb)
             (('bb new-label rev-instrs)
              (list-set! new-bbs new-label
                           (make-bb new-label (map fix rev-instrs))))
             (else (error renumber-labels "impossible to be here!")))))
       b label))
    new-bbs))

(define (code->vector code)
  (let ((v (make-list (+ (code-last-label code) 1))))
    (for-each (lambda (bb) (list-set! v (bb-label bb) bb))
              (code-rev-bbs code))
    v))

(define (resolve-toplevel-labels! bbs)
  (for-each
   (lambda (i)
     (let* ((bb (list-ref bbs i))
            (rev-instrs (bb-rev-instrs bb)))
       (bb-rev-instrs-set!
        bb
        (map (lambda (instr)
               (display instr)(newline)
               (match instr
                 (`(,(and opcode (or 'call-toplevel 'jump-toplevel)) ,arg)
                  `(,opcode ,(prc-entry-label arg)))
                 (instr instr)))
             rev-instrs))))
   (iota (length bbs))))
