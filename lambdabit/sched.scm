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

(define-module (lambdabit sched)
  #:use-module (srfi srfi-1)
  #:use-module (ice-9 match)
  #:use-module (lambdabit ir)
  #:use-module (lambdabit back-end))

(module-export-all! (current-module))

;; Basic block scheduling.
(define (schedule bbs)
  (linearize (reorder! bbs)))

;;-----------------------------------------------------------------------------

(define (reorder! bbs)
  (define done (make-vector (vector-length bbs) #f))
  (define (unscheduled? label) (not (vector-ref done label)))
  (define (label-refs instrs todo)
    (fold (lambda (instr p)
            (if (memq (car instr) '(closure call-toplevel jump-toplevel))
                (cons (cons (cadr instr) todo) p)
                p))
          '(())
          instrs))
  (define (schedule-here label new-label todo)
    (match (vector-ref bbs label)
      ((bb label (and rev-instrs `(,jump . ,rest)))
         (define new-todo (label-refs rev-instrs todo))
         (vector-set! bbs  label (make-bb new-label rev-instrs))
         (vector-set! done label #t)
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
  
  (let ((len (vector-length bbs)))
    (renumber-labels bbs (make-vector len 1) len)))

;;-----------------------------------------------------------------------------

;; State for linearize.
;; Ugly, but better than having everything as an internal define
(define rev-code '())
(define pos 0)
(define todo (cons '() '()))
(define bbs #f)
(define dumped #f)

(define (emit x)
  (set! pos (+ pos 1))
  (set! rev-code (cons x rev-code)))

(define (get fallthrough-to-next?)
  (define r-todo (cdr todo))
  (cond
   (fallthrough-to-next?
    (match r-todo
      ((cons (and label-pos `(,label . ,_)) rest)
       (unless (pair? rest)
         (set-car! todo todo))
       (set-cdr! todo rest)
       label)))
   (else 
    (let ((best-label-pos
           (fold (lambda (x p)
                   (if (and (not (vector-ref dumped (car x)))
                            (or (not p)
                                (> (cdr x) (cdr p))))
                            (cons x p)
                            p))
                 '() r-todo)))
      (and best-label-pos (car best-label-pos))))))
                 
(define (next)
  (any (lambda (x)
         (let ((label-pos (cdr todo)))
           (and (not (vector-ref dumped (car label-pos))) x)))
       todo))

(define (schedule! label tail?)
  (let ((label-pos (cons label pos)))
    (if tail?
        (let ((cell (cons label-pos '())))
          (set-cdr! (car todo) cell)
          (set-car! todo cell))
        (let ((cell (cons label-pos (cdr todo))))
          (set-cdr! todo cell)
          (when (eq? (car todo) todo)
            (set-car! todo cell))))))

(define (dump)
  (let lp ((fallthrough-to-next? #t))
    (let ((label (get fallthrough-to-next?)))
      (when label
        (cond ((not (vector-ref dumped label))
               (vector-set! dumped label #t)
               (lp (dump-bb label)))
              (else (lp fallthrough-to-next?)))))))

(define (dump-bb label)
  (match (vector-ref bbs label)
    ((bb label `(,jump . ,rest))
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
       (_
        (emit jump)
        #f)))))

(define (linearize cur-bbs)
  (set! bbs    cur-bbs)
  (set! dumped (make-vector (vector-length cur-bbs) #f))
  (set-car! todo todo) ;; make fifo
  (schedule! 0 #f)
  (dump)
  (reverse rev-code))
