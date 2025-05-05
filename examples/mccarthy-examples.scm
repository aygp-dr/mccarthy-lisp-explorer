;; mccarthy-examples.scm - Examples from McCarthy's original paper
;;
;; This file contains direct implementations of the examples from
;; McCarthy's 1960 paper "Recursive Functions of Symbolic Expressions
;; and Their Computation by Machine, Part I."

;; Add our source directory to the load path
(add-to-load-path "..")

(use-modules (ap mccarthy))

;; Display a title banner
(display "\nExamples from McCarthy's 1960 Paper\n")
(display "=================================\n\n")

;; Section 3a: Conditional Expressions

(display "Section 3a: Conditional Expressions\n")
(display "-------------------------------\n\n")

(display "McCarthy introduced a notation for conditional expressions:\n")
(display "(cond (p₁ e₁) (p₂ e₂) ... (pₙ eₙ))\n\n")

(display "In our implementation, these are evaluated with the eval function.\n")
(display "For example, here's a conditional expression in our evaluator:\n\n")

(define cond-example 
  '(cond ((atom? (quote A)) (quote is-atom))
         (t (quote not-atom))))

(display "Expression: ")
(display cond-example)
(display "\nResult: ")
(display (eval cond-example '((t . #t))))
(display "\n\n")

;; Section 3b: Recursive Function Definitions

(display "Section 3b: Recursive Function Definitions\n")
(display "--------------------------------------\n\n")

(display "McCarthy used the label construct for recursive functions:\n")
(display "(label f (lambda (args) ...))\n\n")

(display "Here's the factorial function from the paper (Section 3c):\n\n")

(define factorial-fn
  '(label factorial 
     (lambda (n) 
       (cond ((eq n 0) 1)
             (t (times n (factorial (sub1 n))))))))

(define math-env
  '((t . #t)
    (sub1 . ,(lambda (n) (- n 1)))
    (times . ,*)
    (eq . ,=)))

(display "Expression: ")
(display factorial-fn)
(display "\n\n")

(display "Results:\n")
(for-each 
 (lambda (n) 
   (display "factorial(")
   (display n)
   (display ") = ")
   (display (apply factorial-fn (list n) math-env))
   (newline))
 '(0 1 2 3 4 5))
(newline)

;; Section 3c: Elementary S-functions

(display "Section 3c: Elementary S-functions\n")
(display "-------------------------------\n\n")

(display "McCarthy defined five elementary operations on S-expressions:\n")
(display "atom?, eq?, car, cdr, and cons\n\n")

(display "These five operations form the foundation of all LISP functions.\n")
(display "Our implementation includes them directly, named exactly as in the paper.\n\n")

(define examples 
  '(((atom? (quote A)) . #t)
    ((atom? (quote (A B))) . #f)
    ((eq? (quote A) (quote A)) . #t)
    ((eq? (quote A) (quote B)) . #f)
    ((car (quote (A B C))) . A)
    ((cdr (quote (A B C))) . (B C))
    ((cons (quote A) (quote (B C))) . (A B C))))

(for-each
 (lambda (example)
   (let ((expr (car example))
         (expected (cdr example)))
     (display "Expression: ")
     (display expr)
     (display "\nExpected: ")
     (display expected)
     (display "\nResult:   ")
     (display (eval expr '()))
     (display "\n\n")))
 examples)

;; Section 3d: Some Functions on S-expressions

(display "Section 3d: Some Functions on S-expressions\n")
(display "---------------------------------------\n\n")

(display "McCarthy defined several higher-level functions on S-expressions.\n")
(display "Here are some examples:\n\n")

(display "1. equal? - Tests if two S-expressions are structurally identical\n")
(display "   (equal? '(A B C) '(A B C)) => ")
(display (equal? '(A B C) '(A B C)))
(display "\n\n")

(display "2. append - Joins two lists\n")
(display "   (append '(A B) '(C D)) => ")
(display (append '(A B) '(C D)))
(display "\n\n")

;; Section 4: The LISP Programming System

(display "Section 4: The LISP Programming System\n")
(display "---------------------------------\n\n")

(display "Section 4 introduces the universal LISP evaluator (eval and apply).\n")
(display "This allows LISP programs represented as S-expressions to be executed.\n\n")

(display "Our implementation includes this evaluator, allowing us to evaluate\n")
(display "LISP expressions represented as S-expressions:\n\n")

(define eval-examples
  '(((quote A) . A)
    ((car (quote (A B C))) . A)
    ((cons (car (quote (A B))) (cdr (quote (C D)))) . (A D))))

(for-each
 (lambda (example)
   (let ((expr (car example))
         (expected (cdr example)))
     (display "Expression: ")
     (display expr)
     (display "\nExpected: ")
     (display expected)
     (display "\nResult:   ")
     (display (eval expr '()))
     (display "\n\n")))
 eval-examples)

(display "For more details, see the original paper in resources/recursive.pdf\n")
(display "and explore our implementation in the src/ directory.\n\n")