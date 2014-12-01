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

(define-module (lambdabit sched)
  #:use-module (srfi srfi-1)
  #:use-module (ice-9 match)
  #:use-module (lambdabit ir)
  #:use-module (lambdabit utils)
  #:use-module (lambdabit back-end))

(module-export-all! (current-module))

;; Basic block scheduling.
(define (schedule bbs)
  (linearize (reorder! bbs)))

;;----------------------------------------------------------------------------

(define (reorder! bbs)
  (define done (make-list (length bbs) #f))
  (define (unscheduled? label)
    ;;(format #t "unscheduled? ~a~%" label)
    (not (list-ref done (if (null? label) 0 label))))
  (define (label-refs instrs todo)
    (fold (lambda (instr p)
            (if (memq (car instr) '(closure call-toplevel jump-toplevel))
                (cons (cons (cadr instr) todo) p)
                p))
          '(())
          instrs))
  (define (schedule-here label new-label todo)
    (match (->list (list-ref bbs label))
      (('bb label (and rev-instrs `(,jump . ,rest)))
       (define new-todo (label-refs rev-instrs todo))
       (list-set! bbs  label (make-bb new-label rev-instrs))
       (list-set! done label #t)
       (match jump
         (`(goto ,label)
          (if (unscheduled? label)
              (schedule-here label (+ new-label 1) new-todo)
              (values (+ new-label 1) new-todo)))
         (`(goto-if-false ,label-then ,label-else)
          (cond ((unscheduled? label-else)
                 (schedule-here label-else
                                (+ new-label 1)
                                (cons label-then new-todo)))
                ((unscheduled? label-then)
                 (schedule-here label-then
                                (+ new-label 1)
                                new-todo))
                (else (values (+ new-label 1) new-todo))))
         (_ (values (+ new-label 1) new-todo))))))
  (define (schedule-todo new-label todo)
    (when (pair? todo)
      (let ((label (car todo)))
        (if (unscheduled? label)
            (call-with-values
                (lambda () (schedule-here label new-label (cdr todo)))
              schedule-todo)
            (schedule-todo new-label (cdr todo))))))

  (call-with-values (lambda () (schedule-here 0 0 '()))
    schedule-todo)
  
  (let ((len (length bbs)))
    (renumber-labels bbs (make-list len 1) len)))

;;-----------------------------------------------------------------------------

;; State for linearize.
;; Ugly, but better than having everything as an internal define
(define rev-code '())
(define pos 0)
(define todo (new-queue)) ; NOTE: it's a bi-directioin list
(define bbs #f)
(define dumped #f)

(define (emit x)
  (set! pos (+ pos 1))
  (set! rev-code (cons x rev-code)))

(define (get fallthrough-to-next?)
  (cond
   ((queue-empty? todo) #f)
   (else
    (cond
     (fallthrough-to-next?
      (match (stack-top todo)
        ((label . _)
         ;;(format #t "LABEL: ~a~%" label)
         (stack-pop! todo)
         label)))
     (else
      (let ((best-label-pos
             (fold (lambda (x p)
                     (if (and (not (list-ref dumped (car x)))
                              (or (not p)
                                  (> (cdr x) (cdr p))))
                         x
                         #f))
                   #f (car todo))))
        (and best-label-pos (car best-label-pos))))))))

(define (next)
  (any (lambda (label-pos)
         ;;(format #t "BBB: ~a~%" label-pos)
         ;;(format #t "TODO: ~a~%" todo)
         (and (not (list-ref dumped (car label-pos))) label-pos))
       (car todo)))

(define (schedule! label tail?)
  (let ((label-pos (cons label pos)))
    (if tail?
        (stack-push! todo label-pos)
        (queue-in! todo label-pos))))

(define (dump)
  (let lp ((fallthrough-to-next? #t))
    (let ((label (get fallthrough-to-next?)))
      (when label
        (cond ((not (list-ref dumped label))
               (list-set! dumped label #t)
               (lp (dump-bb label)))
              (else (lp fallthrough-to-next?)))))))

(define (dump-bb label)
  (match (->list (list-ref bbs label))
    (('bb label (jump . rest))
     (emit label)
     (for-each (lambda (instr)
                 (match instr
                   (`(,(or 'closure 'call-toplevel) ,arg)
                    (schedule! arg #t))
                   (_ #t))
                 (emit instr))
               (reverse rest))  
     (match jump
       (`(goto ,label)
        (schedule! label #f)
        (if (not (equal? label (next)))
            (begin (emit jump) #f)
            #t))
       (`(goto-if-false ,label-then ,label-else)
        (schedule! label-then #f)
        (schedule! label-else #f)
        (cond ((equal? label-else (next))
               (emit (list 'goto-if-false label-then))
               #t)
              ((equal? label-then (next))
               (emit (list 'prim '%not))
               (emit (list 'goto-if-false label-else))
               #t)
              (else
               (emit (list 'goto-if-false label-then))
               (emit (list 'goto label-else))
               #f)))
       (`(jump-toplevel ,label)
        (schedule! label #f)
        ;; it is not correct to remove jump-toplevel when label is next
        (emit jump)
        #f)
       (_ (emit jump)
          #f)))))

(define (linearize cur-bbs)
  (set! bbs cur-bbs)
  (set! dumped (make-list (length cur-bbs) #f))
;;  (set! todo (new-queue)) ; make fifo
  (schedule! 0 #f)
  (dump)
  (reverse rev-code))
