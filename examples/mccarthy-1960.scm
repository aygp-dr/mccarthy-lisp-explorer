;; mccarthy-1960.scm - Direct implementation of examples from McCarthy's 1960 paper
;;
;; This file recreates examples from John McCarthy's 1960 paper
;; "Recursive Functions of Symbolic Expressions and Their Computation by Machine"

;; Add our source directory to the load path
(add-to-load-path "..")

;; Import our modules
(use-modules (ap mccarthy core-functions)
             (ap mccarthy evaluator))

;; Display a title banner
(display "\nMcCarthy's 1960 LISP Examples\n")
(display "===========================\n\n")

;; Enable tracing for demonstration
(trace-on)

;; ---- Section 3: Functions of S-expressions ----

(display "Section 3: Functions of S-expressions\n")
(display "==================================\n\n")

;; Basic S-expression operations
(display "Basic operations on S-expressions:\n\n")

(display "1. atom? - test if an expression is an atom\n")
(display "   (atom? 'A) => ")
(display (atom? 'A))
(display "\n   (atom? '(A B)) => ")
(display (atom? '(A B)))
(display "\n\n")

(display "2. eq? - test if two atoms are identical\n")
(display "   (eq? 'A 'A) => ")
(display (eq? 'A 'A))
(display "\n   (eq? 'A 'B) => ")
(display (eq? 'A 'B))
(display "\n\n")

(display "3. car - first element of a list\n")
(display "   (car '(A B C)) => ")
(display (car '(A B C)))
(display "\n\n")

(display "4. cdr - rest of a list\n")
(display "   (cdr '(A B C)) => ")
(display (cdr '(A B C)))
(display "\n\n")

(display "5. cons - construct a list\n")
(display "   (cons 'A '(B C)) => ")
(display (cons 'A '(B C)))
(display "\n\n")

;; ---- Higher-level functions ----

(display "Higher-level functions from the paper:\n\n")

(display "1. null? - test if a list is empty\n")
(display "   (null? '()) => ")
(display (null? '()))
(display "\n   (null? '(A)) => ")
(display (null? '(A)))
(display "\n\n")

(display "2. equal? - test structural equality of S-expressions\n")
(display "   (equal? '(A B) '(A B)) => ")
(display (equal? '(A B) '(A B)))
(display "\n   (equal? '(A B) '(A C)) => ")
(display (equal? '(A B) '(A C)))
(display "\n\n")

(display "3. append - join two lists\n")
(display "   (append '(A B) '(C D)) => ")
(display (append '(A B) '(C D)))
(display "\n\n")

(display "4. subst - substitutes y for all occurrences of x in z\n")
(display "   (subst 'A 'B '(C A D A)) => ")
(display (subst 'A 'B '(C A D A)))
(display "\n\n")

(display "5. member - checks if x is a member of list y\n")
(display "   (member 'A '(B C A D)) => ")
(display (member 'A '(B C A D)))
(display "\n   (member 'E '(B C A D)) => ")
(display (member 'E '(B C A D)))
(display "\n\n")

(display "6. apply-to-all - applies a function to all elements of a list\n")
(display "   (apply-to-all (lambda (x) (cons 'X x)) '((A) (B) (C))) => ")
(display (apply-to-all (lambda (x) (cons 'X x)) '((A) (B) (C))))
(display "\n\n")

;; ---- Mathematical functions ----

(display "McCarthy's mathematical functions:\n\n")

(display "1. factorial - computes n! recursively\n")
(display "   (factorial 5) => ")
(display (factorial 5))
(display "\n\n")

(display "2. gcd-recursive - computes greatest common divisor\n")
(display "   (gcd-recursive 36 24) => ")
(display (gcd-recursive 36 24))
(display "\n\n")

(display "3. sqrt-approx - computes square root by Newton's method\n")
(display "   (sqrt-approx 16) => ")
(display (sqrt-approx 16))
(display "\n\n")

;; ---- Section 4: The LISP Evaluator ----

(display "Section 4: The LISP Evaluator\n")
(display "===========================\n\n")

;; Create a base environment with some additional bindings
(define env (extend-env 
             '((t . #t)
               (nil . ())
               (x . 10)
               (y . 20)
               (list-1 . (A B C))
               (list-2 . (D E F)))
             (make-env)))

(display "Using our LISP evaluator with environment:\n")
(display "  t = #t, nil = (), x = 10, y = 20,\n")
(display "  list-1 = (A B C), list-2 = (D E F)\n\n")

;; Some example expressions to evaluate
(define examples
  '(
    ;; Quote
    (quote hello)
    
    ;; Symbol lookup
    x
    
    ;; Primitive function calls
    (car list-1)
    (cdr list-1)
    (cons x list-1)
    
    ;; Higher-level functions
    (append list-1 list-2)
    (apply-to-all car (quote ((A B) (C D) (E F))))
    
    ;; Conditional expression
    (cond ((eq? x 10) (quote is-ten))
          (t (quote not-ten)))
          
    ;; Lambda expression
    ((lambda (a b) (cons a b)) (quote NEW) list-1)
    
    ;; Recursive function (using label)
    ((label sum-list
            (lambda (lst)
                   (cond ((null? lst) 0)
                         (t (+ (car lst) (sum-list (cdr lst)))))))
     (quote (1 2 3 4 5)))
     
    ;; Nested evaluation with multiple expressions
    (cons (car (quote (A B C)))
          (append (quote (X Y)) (quote (Z))))
  ))

;; Evaluate each example
(for-each
 (lambda (expr)
   (display "Expression: ")
   (display expr)
   (display "\nResult: ")
   (display (eval expr env))
   (display "\n\n"))
 examples)

(display "For more details, see McCarthy's original paper and our implementation.\n")
(display "Explore the source code in src/ap/mccarthy/ directory.\n\n")

;; Disable tracing
(trace-off)