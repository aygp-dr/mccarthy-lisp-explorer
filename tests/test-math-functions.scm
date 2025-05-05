;; test-math-functions.scm - Tests for mathematical functions
;;
;; Tests for factorial, GCD, and sqrt functions from McCarthy's paper section 3

(add-to-load-path "..")

(use-modules (ap mccarthy))

(load "../examples/math-functions.scm")

(display "Running mathematical function tests...\n")
(newline)

;; Test factorial function
(display "Testing factorial function...\n")

;; Test with McCarthy's evaluator
(define factorial-results
  (map (lambda (n) (apply factorial-fn (list n) math-env))
       '(0 1 2 3 4 5)))

(define expected-factorial-results '(1 1 2 6 24 120))

(display "McCarthy's evaluator factorial results: ")
(display factorial-results)
(newline)
(display "Expected results: ")
(display expected-factorial-results)
(newline)
(display "Correct? ")
(display (equal? factorial-results expected-factorial-results))
(newline)
(newline)

;; Test with native implementation
(display "Testing native factorial implementation...\n")
(define native-factorial-results
  (map factorial '(0 1 2 3 4 5)))

(display "Native factorial results: ")
(display native-factorial-results)
(newline)
(display "Expected results: ")
(display expected-factorial-results)
(newline)
(display "Correct? ")
(display (equal? native-factorial-results expected-factorial-results))
(newline)
(newline)

;; Test GCD function
(display "Testing GCD function...\n")

;; Test with McCarthy's evaluator
(define gcd-test-cases '((48 18) (100 75) (35 49) (120 55) (9 9) (17 5)))
(define gcd-results
  (map (lambda (pair) 
         (apply gcd-fn (list (car pair) (cadr pair)) math-env))
       gcd-test-cases))

(define expected-gcd-results '(6 25 7 5 9 1))

(display "McCarthy's evaluator GCD results: ")
(display gcd-results)
(newline)
(display "Expected results: ")
(display expected-gcd-results)
(newline)
(display "Correct? ")
(display (equal? gcd-results expected-gcd-results))
(newline)
(newline)

;; Test with native implementation
(display "Testing native GCD implementation...\n")
(define native-gcd-results
  (map (lambda (pair)
         (gcd-recursive (car pair) (cadr pair)))
       gcd-test-cases))

(display "Native GCD results: ")
(display native-gcd-results)
(newline)
(display "Expected results: ")
(display expected-gcd-results)
(newline)
(display "Correct? ")
(display (equal? native-gcd-results expected-gcd-results))
(newline)
(newline)

;; Test sqrt function
(display "Testing sqrt approximation function...\n")

;; Test with McCarthy's evaluator
(define sqrt-test-cases '(1 4 9 16 25 100))
(define sqrt-results
  (map (lambda (n) 
         (apply sqrt-fn (list n) sqrt-env))
       sqrt-test-cases))

(define expected-sqrt-results
  (map sqrt sqrt-test-cases))

(define (close-enough? x y)
  (< (abs (- x y)) 0.01))

(define (lists-close-enough? lst1 lst2)
  (if (or (null? lst1) (null? lst2))
      #t
      (and (close-enough? (car lst1) (car lst2))
           (lists-close-enough? (cdr lst1) (cdr lst2)))))

(display "McCarthy's evaluator sqrt results: ")
(for-each (lambda (x) (format #t "~,5f " x)) sqrt-results)
(newline)
(display "Expected results: ")
(for-each (lambda (x) (format #t "~,5f " x)) expected-sqrt-results)
(newline)
(display "Close enough? ")
(display (lists-close-enough? sqrt-results expected-sqrt-results))
(newline)
(newline)

;; Test with native implementation
(display "Testing native sqrt implementation...\n")
(define native-sqrt-results
  (map sqrt-approx sqrt-test-cases))

(display "Native sqrt results: ")
(for-each (lambda (x) (format #t "~,5f " x)) native-sqrt-results)
(newline)
(display "Expected results: ")
(for-each (lambda (x) (format #t "~,5f " x)) expected-sqrt-results)
(newline)
(display "Close enough? ")
(display (lists-close-enough? native-sqrt-results expected-sqrt-results))
(newline)
(newline)

;; Test with trace enabled if requested
(let ((trace-enabled? (getenv "MCCARTHY_TRACE")))
  (when trace-enabled?
    (trace-on)
    (display "Trace mode enabled. Computing factorial(3) with tracing:\n")
    (factorial 3)
    (newline)
    
    (display "Computing GCD(48, 18) with tracing:\n")
    (gcd-recursive 48 18)
    (newline)
    
    (display "Computing sqrt(9) with tracing (simplified):\n")
    (sqrt-approx 9)
    (trace-off)))

(display "All mathematical function tests completed.\n")