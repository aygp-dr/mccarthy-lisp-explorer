;; test-mccarthy-functions.scm - Tests for McCarthy's Lisp functions
;;
;; This file provides tests for the functions implemented from McCarthy's
;; 1960 paper on recursive functions of symbolic expressions.

;; Add our source directory to the load path
(add-to-load-path "..")

;; Import our modules
(use-modules (ap mccarthy core-functions)
             (ap mccarthy evaluator)
             (srfi srfi-64)) ; Testing framework

;; Begin the test suite
(test-begin "mccarthy-1960-functions")

;; ---- Test primitive functions ----

(test-group "primitive-functions"
  (test-assert "atom? recognizes symbols" (atom? 'a))
  (test-assert "atom? rejects lists" (not (atom? '(a b))))
  (test-assert "atom? rejects empty list" (not (atom? '())))
  
  (test-assert "eq? with identical atoms" (eq? 'a 'a))
  (test-assert "eq? with different atoms" (not (eq? 'a 'b)))
  
  (test-equal "car of list" 'a (car '(a b c)))
  (test-equal "cdr of list" '(b c) (cdr '(a b c)))
  (test-equal "cons creates list" '(a b c) (cons 'a '(b c)))
)

;; ---- Test higher-level functions ----

(test-group "higher-level-functions"
  (test-assert "null? on empty list" (null? '()))
  (test-assert "null? on non-empty list" (not (null? '(a))))
  
  (test-assert "equal? with identical lists" (equal? '(a b) '(a b)))
  (test-assert "equal? with different lists" (not (equal? '(a b) '(a c))))
  
  (test-equal "append joins lists" '(a b c d) (append '(a b) '(c d)))
  (test-equal "append with empty first list" '(c d) (append '() '(c d)))
  (test-equal "append with empty second list" '(a b) (append '(a b) '()))
  
  (test-equal "pair creates pairs" '((a 1) (b 2)) (pair '(a b) '(1 2)))
  
  (test-equal "assoc finds association" '(b 2) (assoc 'b '((a 1) (b 2) (c 3))))
  (test-equal "assoc returns #f for missing key" #f (assoc 'z '((a 1) (b 2))))
  
  (test-equal "apply-to-all applies function" 
             '(2 3 4) 
             (apply-to-all (lambda (x) (+ x 1)) '(1 2 3)))
             
  (test-equal "subst substitutes correctly"
             '(x b x d)
             (subst 'a 'x '(a b a d)))
             
  (test-assert "member finds element" (member 'b '(a b c)))
  (test-assert "member returns #f for missing element" (not (member 'z '(a b c))))
)

;; ---- Test mathematical functions ----

(test-group "mathematical-functions"
  (test-equal "factorial of 0" 1 (factorial 0))
  (test-equal "factorial of 5" 120 (factorial 5))
  
  (test-equal "gcd of 48 and 18" 6 (gcd-recursive 48 18))
  (test-equal "gcd of 17 and 5" 1 (gcd-recursive 17 5))
  
  ;; Square root test with a small epsilon for floating point comparison
  (let ((result (sqrt-approx 16)))
    (test-assert "sqrt of 16 is approximately 4"
                 (< (abs (- result 4.0)) 0.01)))
)

;; ---- Test evaluator functions ----

(test-group "evaluator"
  (let ((env (extend-env '((x . 10) (y . 20) (t . #t) (nil . ())) (make-env))))
    
    (test-equal "eval symbol lookup" 10 (eval 'x env))
    
    (test-equal "eval quote" 'hello (eval '(quote hello) env))
    
    (test-equal "eval car" 'a (eval '(car (quote (a b c))) env))
    
    (test-equal "eval cond" 'is-ten
                (eval '(cond ((eq? x 10) (quote is-ten))
                             (t (quote not-ten)))
                      env))
                      
    (test-equal "eval lambda" '(new a b c)
                (eval '((lambda (a b) (cons a b))
                        (quote new)
                        (quote (a b c)))
                      env))
                      
    (test-equal "eval label (recursive function)" 15
                (eval '((label sum-list
                                (lambda (lst)
                                 (cond ((null? lst) 0)
                                       (t (+ (car lst) (sum-list (cdr lst)))))))
                        (quote (1 2 3 4 5)))
                      env))
  )
)

;; Finish testing
(test-end "mccarthy-1960-functions")

;; Display test results
(test-exit)