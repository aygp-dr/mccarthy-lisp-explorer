#!/usr/bin/env guile3
!#

;; interactive-examples.scm - Interactive demonstrations of McCarthy's LISP
;;
;; This script provides interactive examples of the concepts from McCarthy's paper.

;; Add our source directory to the load path
(add-to-load-path ".")

(use-modules (ap mccarthy))

;; Display a separator line
(define (display-separator)
  (display "\n")
  (display (make-string 70 #\-))
  (display "\n\n"))

;; Display a section header
(define (display-section title)
  (display-separator)
  (display title)
  (display "\n\n"))

;; Start the interactive examples
(display "\nMcCarthy's LISP Explorer: Interactive Examples\n")
(display "============================================\n\n")
(display "This script demonstrates key concepts from McCarthy's 1960 paper\n")
(display "\"Recursive Functions of Symbolic Expressions and Their Computation by Machine, Part I.\"\n\n")
(display "Press Enter after each example to continue...\n")

;; Section 1: Basic S-expressions and primitives
(display-section "1. Basic S-expressions and Primitives")

(display "In McCarthy's LISP, everything is an S-expression (symbolic expression).\n")
(display "S-expressions can be atomic symbols or lists of S-expressions.\n\n")

(display "The five elementary operations are:\n")
(display "1. atom? - Tests if an expression is an atomic symbol\n")
(display "2. eq? - Tests if two atomic symbols are identical\n")
(display "3. car - Returns the first element of a list\n")
(display "4. cdr - Returns the rest of a list\n")
(display "5. cons - Constructs a new list by adding an element to the front\n\n")

(display "Examples:\n")
(display "(atom? 'A) => ")
(display (atom? 'A))
(display "\n(atom? '(A B)) => ")
(display (atom? '(A B)))
(display "\n(eq? 'A 'A) => ")
(display (eq? 'A 'A))
(display "\n(eq? 'A 'B) => ")
(display (eq? 'A 'B))
(display "\n(car '(A B C)) => ")
(display (car '(A B C)))
(display "\n(cdr '(A B C)) => ")
(display (cdr '(A B C)))
(display "\n(cons 'A '(B C)) => ")
(display (cons 'A '(B C)))
(display "\n")

(read-line)

;; Section 2: Recursive Functions
(display-section "2. Recursive Functions")

(display "McCarthy's paper introduced recursive functions as a programming paradigm.\n")
(display "Here are examples of the recursive functions described in the paper:\n\n")

;; Enable tracing to show the recursive steps
(trace-on)

(display "Factorial function:\n")
(display "(factorial 5) => ")
(display (factorial 5))
(display "\n\n")

(display "GCD (greatest common divisor) function:\n")
(display "(gcd-recursive 48 18) => ")
(display (gcd-recursive 48 18))
(display "\n\n")

(display "Square root approximation (Newton's method):\n")
(display "(sqrt-approx 16) => ")
(display (sqrt-approx 16))
(display "\n")

;; Disable tracing for the rest of the examples
(trace-off)

(read-line)

;; Section 3: List Processing Functions
(display-section "3. List Processing Functions")

(display "McCarthy's LISP introduces several functions for processing lists:\n\n")

(display "null? - Tests if a list is empty:\n")
(display "(null? '()) => ")
(display (null? '()))
(display "\n(null? '(A)) => ")
(display (null? '(A)))
(display "\n\n")

(display "equal? - Tests if two S-expressions are identical:\n")
(display "(equal? '(A B C) '(A B C)) => ")
(display (equal? '(A B C) '(A B C)))
(display "\n(equal? '(A B) '(A C)) => ")
(display (equal? '(A B) '(A C)))
(display "\n\n")

(display "append - Joins two lists:\n")
(display "(append '(A B) '(C D)) => ")
(display (append '(A B) '(C D)))
(display "\n\n")

(display "pair - Pairs corresponding elements in two lists:\n")
(display "(pair '(A B C) '(1 2 3)) => ")
(display (pair '(A B C) '(1 2 3)))
(display "\n")

(read-line)

;; Section 4: The Universal Evaluator (eval/apply)
(display-section "4. The Universal Evaluator (eval/apply)")

(display "The most profound contribution of McCarthy's paper was the universal evaluator,\n")
(display "which could interpret and execute LISP programs represented as S-expressions.\n\n")

(display "This consisted of two mutually recursive functions: eval and apply.\n\n")

(display "Examples of eval:\n")
(display "(eval '(quote A) '()) => ")
(display (eval '(quote A) '()))
(display "\n\n")

(display "(eval '(car (quote (A B C))) '()) => ")
(display (eval '(car (quote (A B C))) '()))
(display "\n\n")

(display "(eval '(cond ((atom? (quote A)) (quote atom))\n")
(display "              (t (quote not-atom)))\n")
(display "       '((t . #t))) => ")
(display (eval '(cond ((atom? (quote A)) (quote atom))
                     (t (quote not-atom)))
                  '((t . #t))))
(display "\n\n")

;; Math environment for factorial example
(define math-env
  '((t . #t)
    (sub1 . ,(lambda (n) (- n 1)))
    (times . ,*)
    (zero . ,(lambda (n) (= n 0)))))

;; Factorial function using McCarthy's label construct
(define factorial-fn
  '(label factorial 
     (lambda (n) 
       (cond ((zero n) 1)
             (t (times n (factorial (sub1 n))))))))

(display "Factorial using McCarthy's evaluator:\n")
(display "(apply factorial-fn '(5) math-env) => ")
(display (apply factorial-fn '(5) math-env))
(display "\n")

(read-line)

;; Final section: Conclusion
(display-section "Conclusion")

(display "This completes our tour of the key concepts from McCarthy's 1960 paper.\n\n")
(display "You've seen:\n")
(display "1. The five primitive operations for S-expressions\n")
(display "2. Recursive functions for computation\n")
(display "3. List processing functions\n")
(display "4. The universal evaluator (eval/apply)\n\n")

(display "To explore more:\n")
(display "- Read McCarthy's original paper (resources/recursive.pdf)\n")
(display "- Check the examples directory for more code samples\n")
(display "- Look at the implementation in src/ap/mccarthy/\n")
(display "- Try the exercises in EXERCISES.org\n\n")

(display "Thank you for exploring McCarthy's LISP!\n")
(display-separator)