;; hello-world.scm - Simple introduction to S-expressions
;;
;; This file introduces the basic concepts of McCarthy's LISP

;; Add our source directory to the load path
(add-to-load-path "..")

(use-modules (ap mccarthy))

;; Display a title banner
(display "\n")
(display "McCarthy's LISP - Hello, World!\n")
(display "==============================\n\n")

;; 1. S-expressions
(display "S-expressions are the basic data structures in LISP.\n")
(display "They can be atomic symbols or lists of S-expressions.\n\n")

(display "Examples of S-expressions:\n")
(display "  - Atomic symbol: 'A\n")
(display "  - List: '(A B C)\n")
(display "  - Nested list: '(A (B C) D)\n\n")

;; 2. The five primitive operations
(display "McCarthy defined five primitive operations for S-expressions:\n\n")

;; atom?
(display "1. atom? - Tests if an expression is an atomic symbol\n")
(display "   (atom? 'A) => ")
(display (atom? 'A))
(display "\n   (atom? '(A B)) => ")
(display (atom? '(A B)))
(display "\n\n")

;; eq?
(display "2. eq? - Tests if two atomic symbols are identical\n")
(display "   (eq? 'A 'A) => ")
(display (eq? 'A 'A))
(display "\n   (eq? 'A 'B) => ")
(display (eq? 'A 'B))
(display "\n\n")

;; car
(display "3. car - Returns the first element of a list\n")
(display "   (car '(A B C)) => ")
(display (car '(A B C)))
(display "\n   (car '((A B) C)) => ")
(display (car '((A B) C)))
(display "\n\n")

;; cdr
(display "4. cdr - Returns the rest of a list\n")
(display "   (cdr '(A B C)) => ")
(display (cdr '(A B C)))
(display "\n   (cdr '((A B) C)) => ")
(display (cdr '((A B) C)))
(display "\n\n")

;; cons
(display "5. cons - Constructs a new list by adding an element to the front\n")
(display "   (cons 'A '(B C)) => ")
(display (cons 'A '(B C)))
(display "\n   (cons '(A B) '(C D)) => ")
(display (cons '(A B) '(C D)))
(display "\n\n")

;; 3. Building more complex functions
(display "These five primitives can be used to build more complex functions.\n")
(display "For example, here's how to get the second element of a list:\n")
(display "   (car (cdr '(A B C))) => ")
(display (car (cdr '(A B C))))
(display "\n\n")

;; 4. Higher-level functions
(display "McCarthy's LISP also defined higher-level functions like append and equal:\n")

(display "append joins two lists:\n")
(display "   (append '(A B) '(C D)) => ")
(display (append '(A B) '(C D)))
(display "\n\n")

(display "equal? tests if two S-expressions are structurally identical:\n")
(display "   (equal? '(A B C) '(A B C)) => ")
(display (equal? '(A B C) '(A B C)))
(display "\n   (equal? '(A B) '(A C)) => ")
(display (equal? '(A B) '(A C)))
(display "\n\n")

;; 5. The concept of "code as data"
(display "One of the most powerful ideas in LISP is that code and data\n")
(display "have the same representation: both are S-expressions.\n\n")

(display "This allows programs to manipulate other programs as data.\n")
(display "This concept led to McCarthy's universal LISP evaluator,\n")
(display "which could interpret LISP programs represented as S-expressions.\n\n")

;; Demo of a simple quoted expression
(define example-code '(cons 'A '(B C)))
(display "Here's an example of code as an S-expression:\n")
(display "   example-code = ")
(display example-code)
(display "\n\n")

(display "And here's the result of evaluating that code:\n")
(display "   (eval example-code '()) => ")
(display (eval example-code '()))
(display "\n\n")

;; Conclusion
(display "This concludes our brief introduction to McCarthy's LISP.\n")
(display "For more examples, see the other files in the examples/ directory.\n")
(display "To explore the implementation, check out the source code in src/.\n\n")