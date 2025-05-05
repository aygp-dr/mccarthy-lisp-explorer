;;; s-expressions.scm -- Basic S-expression operations
;;;
;;; Implementation of McCarthy's core S-expression operations

;; McCarthy's paper defines these primitives:
;; 1. atom - predicate that returns true for atomic symbols
;; 2. eq - equality predicate for atomic symbols
;; 3. car - extracts first element of a list (stands for "Contents of Address Register")
;; 4. cdr - extracts rest of a list (stands for "Contents of Decrement Register")
;; 5. cons - constructs a new list by adding an element to the front

;; Many of these are already built into Scheme, but we'll define them
;; exactly as McCarthy described them for educational purposes

;; atom predicate - tests if expression is an atomic symbol
;; In McCarthy's paper, numbers are not considered atoms, only symbols
(define (mccarthy-atom? x)
  (and (not (pair? x)) (not (null? x))))

;; eq predicate - tests if two atomic symbols are identical
(define (mccarthy-eq? x y)
  (and (mccarthy-atom? x) 
       (mccarthy-atom? y)
       (eq? x y)))

;; car, cdr, and cons are already primitives in Scheme
;; but we'll define wrappers for consistency
(define (mccarthy-car x)
  (if (pair? x) 
      (car x)
      (error "car: argument must be a pair")))

(define (mccarthy-cdr x)
  (if (pair? x)
      (cdr x)
      (error "cdr: argument must be a pair")))

(define (mccarthy-cons x y)
  (cons x y))

;; Additional helper functions
(define (mccarthy-list . args)
  args)

;; Test our definitions
(define test-atom (mccarthy-atom? 'A))            ;; #t
(define test-non-atom (mccarthy-atom? '(A B)))    ;; #f

(define test-eq1 (mccarthy-eq? 'A 'A))            ;; #t
(define test-eq2 (mccarthy-eq? 'A 'B))            ;; #f

(define test-cons (mccarthy-cons 'A '(B C)))      ;; (A B C)
(define test-car (mccarthy-car '(A B C)))         ;; A
(define test-cdr (mccarthy-cdr '(A B C)))         ;; (B C)
