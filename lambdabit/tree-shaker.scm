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

(define-module (lambdabit tree-shaker)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-11)
  #:use-module (lambdabit utils)
  #:use-module (lambdabit ir)
  #:use-module (lambdabit back-end)
  #:export (tree-shake!))

(define (tree-shake! bbs)
  (tighten-jump-cascades! bbs)
  (remove-useless-bbs! bbs))

(define (bbs->ref-counts bbs)
  (define ref-counts (make-list (length bbs) 0))
  (define (visit label)
    (let ((ref-count (list-ref ref-counts label)))
      (list-set! ref-counts label (+ ref-count 1))
      (when (= ref-count 0)
        (for-each
         (lambda (instr)
           (match instr
             (('goto arg)
              (visit arg))
             (('goto-if-false a1 a2)
              (visit a1)
              (visit a2))
             (((or 'closure 'call-toplevel 'jump-toplevel) arg)
              (visit arg))
             (else #f)))
         (bb-rev-instrs (list-ref bbs label))))))
    (visit 0)
    ref-counts)

(define (tighten-jump-cascades! bbs)
  (define ref-counts (bbs->ref-counts bbs))
  (define (resolve label)
    (let ((rev-instrs (bb-rev-instrs (vector-ref bbs label))))
      (and (or (null? (cdr rev-instrs))
               (= (vector-ref ref-counts label) 1))
           rev-instrs)))
  (define (iterate)
    (define changed?
      (let-values (((cur-bb i) (in-indexed (length bbs))))
        (fold
         (lambda (bb ii p)
           (if (> (list-ref ref-counts ii) 0)
               (match bb
                 (('bb label (jump . rest))
                  (match jump
                    (`(goto ,label)
                     (let ((jump-replacement (resolve label)))
                       (if jump-replacement
                           ;; void is non-false, counts as a change
                           (list-set! bbs ii
                                        (make-bb label
                                                 (append jump-replacement rest)))
                           p)))
                    (`(goto-if-false ,label-then ,label-else)
                     (let* ((jump-then-replacement (resolve label-then))
                            (jump-else-replacement (resolve label-else))
                            (just-jump-then
                             (and jump-then-replacement
                                  (null? (cdr jump-then-replacement))))
                            (just-jump-else
                             (and jump-else-replacement
                                  (null? (cdr jump-else-replacement))))
                            (then-goto (eq? (caar jump-then-replacement) 'goto))
                            (else-goto (eq? (caar jump-else-replacement) 'goto)))
                       (if (and just-jump-then just-jump-else
                                (or then-goto else-goto))
                           ;; void is non-false, counts as a change
                           (list-set!
                            bbs ii
                            (make-bb label
                                     `((goto-if-false
                                        ,(if then-goto
                                             (cadar jump-then-replacement)
                                             label-then)
                                        ,(if else-goto
                                             (cadar jump-else-replacement)
                                             label-else))
                                       . rest)))
                           p)))))
                 (else p))
               p))
         #f cur-bb i)))
    (when changed? (iterate)))
  ;; begin iterate
  (format #t "iterate: ~a~%" (length bbs))
  (iterate))

(define (remove-useless-bbs! bbs)
  (define ref-counts (bbs->ref-counts bbs))
  (define new-label
    (let-values (((bb label) (in-indexed bbs)))
      (fold (lambda (c b l new-label)
              (cond
               ((> c 0)
                (list-set! bbs l (make-bb new-label (bb-rev-instrs b)))
                (1+ new-label))
               (else new-label)))
            0 ref-counts bb label)))
  (renumber-labels bbs ref-counts new-label))
