;; core-functions.scm - Core functions from McCarthy's paper
;;
;; This file implements both the primitive functions and the higher-level 
;; functions described in McCarthy's 1960 paper, section 3.

(define-module (ap mccarthy core-functions)
  #:export (atom? eq? car cdr cons
            null? equal? append pair assoc list
            factorial gcd-recursive sqrt-approx
            trace-on trace-off))

;; ---- Primitive functions (Section 2) ----

;; Display trace information when debugging
(define *trace* #f)

(define (trace-print name args result)
  (when *trace*
    (display "TRACE: ")
    (display name)
    (display args)
    (display " => ")
    (write result)
    (newline)))

(define (trace-on)
  (set! *trace* #t))

(define (trace-off)
  (set! *trace* #f))

;; atom?: Determine if expression is an atom
;; In McCarthy's paper, only symbols are atoms (not numbers, not the empty list)
(define (atom? x)
  (and (not (pair? x)) (not (null? x))))

;; eq?: Equal predicate for atoms
(define (eq? x y)
  (and (atom? x) (atom? y) (eqv? x y)))

;; car: First element of a list (head)
(define (car x)
  (if (pair? x)
      (car x)
      (error "car: Not a pair" x)))

;; cdr: Rest of a list (tail)
(define (cdr x)
  (if (pair? x)
      (cdr x)
      (error "cdr: Not a pair" x)))

;; cons: Construct a list
(define (cons x y)
  (cons x y))

;; Basic Lisp list constructor
(define (list . args)
  args)

;; ---- Higher-level functions (Section 3) ----

;; null?: Test if expression is the empty list
(define (null? x)
  (eq? x '()))

;; equal?: Test if two S-expressions are equal
(define (equal? x y)
  (cond ((and (atom? x) (atom? y))
         (eq? x y))
        ((or (atom? x) (atom? y))
         #f)
        ((equal? (car x) (car y))
         (equal? (cdr x) (cdr y)))
        (else #f)))

;; append: Join two lists
(define (append x y)
  (if (null? x)
      y
      (cons (car x) (append (cdr x) y))))

;; pair: Create a list of pairs
(define (pair x y)
  (cond ((and (null? x) (null? y)) '())
        ((and (not (atom? x))
              (not (atom? y))
              (not (null? x))
              (not (null? y)))
         (cons (list (car x) (car y))
               (pair (cdr x) (cdr y))))
        (else (error "pair: arguments must be lists of equal length"))))

;; assoc: Find an association in an association list
(define (assoc x a)
  (cond ((null? a) #f)
        ((eq? (car (car a)) x) (car a))
        (else (assoc x (cdr a)))))

;; ---- Mathematical functions (Section 3) ----

;; Factorial function - direct recursive implementation
(define (factorial n)
  (let ((result
         (cond ((= n 0) 1)
               (else (* n (factorial (- n 1)))))))
    (trace-print "factorial" (list n) result)
    result))

;; GCD (Greatest Common Divisor) - Euclidean algorithm
(define (gcd-recursive m n)
  (let ((result
         (cond ((= n 0) m)
               (else (gcd-recursive n (remainder m n))))))
    (trace-print "gcd" (list m n) result)
    result))

;; Square root by Newton's method
(define (sqrt-approx a)
  (define (good-enough? x)
    (< (abs (- (* x x) a)) 0.001))
  
  (define (improve x)
    (/ (+ x (/ a x)) 2))
  
  (define (sqrt-iter x)
    (let ((result
           (cond ((good-enough? x) x)
                 (else (sqrt-iter (improve x))))))
      (trace-print "sqrt-iter" (list x) result)
      result))
  
  (sqrt-iter 1.0))