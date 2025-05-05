;; primitives.scm - Basic primitives from McCarthy's paper
;;
;; This file implements the five elementary functions described in
;; McCarthy's 1960 paper "Recursive Functions of Symbolic Expressions
;; and Their Computation by Machine, Part I."

(define-module (mccarthy primitives)
  #:export (atom quote eq car cdr cons))

;; The five elementary functions from McCarthy's paper:
;; 1. atom - Is the expression an atom?
;; 2. eq - Are the two atoms the same?
;; 3. car - First element of a list
;; 4. cdr - Rest of a list
;; 5. cons - Construct a list

;; Display trace information when debugging
(define *debug* #f)

(define (debug-print label expr)
  (when *debug*
    (display label)
    (display ": ")
    (write expr)
    (newline)))

;; atom: Determine if expression is an atom
(define (atom x)
  (debug-print "atom" x)
  (not (pair? x)))

;; eq: Equal predicate for atoms
(define (eq x y)
  (debug-print "eq" (list x y))
  (and (atom x) (atom y) (equal? x y)))

;; car: First element of a list (head)
(define (car x)
  (debug-print "car" x)
  (if (pair? x)
      (car x)
      (error "car: Not a pair" x)))

;; cdr: Rest of a list (tail)
(define (cdr x)
  (debug-print "cdr" x)
  (if (pair? x)
      (cdr x)
      (error "cdr: Not a pair" x)))

;; cons: Construct a list
(define (cons x y)
  (debug-print "cons" (list x y))
  (cons x y))

;; Enable/disable debug printing
(define (set-debug! val)
  (set! *debug* val))