;; math-functions.scm - Mathematical functions from McCarthy's paper
;;
;; Implementation of factorial, GCD, and sqrt-approximation as described
;; in McCarthy's 1960 paper, section 3.

;; Add our source directory to the load path
(add-to-load-path "..")

(use-modules (ap mccarthy))

;; Turn on tracing if environment variable is set
(if (getenv "MCCARTHY_TRACE")
    (trace-on))

;; Environment with math operators for McCarthy's evaluator
(define math-env
  '((t . #t)
    (sub1 . ,(lambda (n) (- n 1)))
    (add1 . ,(lambda (n) (+ n 1)))
    (plus . ,+)
    (minus . ,-)
    (times . ,*)
    (quotient . ,quotient)
    (remainder . ,remainder)
    (lessthan . ,<)
    (greaterthan . ,>)
    (zero . ,(lambda (n) (= n 0)))
    (divide . ,(lambda (a b) (/ a b)))
    (abs . ,abs)
    (square . ,(lambda (x) (* x x)))))

;;; Factorial function
;;; Uses McCarthy's label construct for recursion
(define factorial-fn
  '(label factorial 
     (lambda (n) 
       (cond ((zero n) 1)
             (t (times n (factorial (sub1 n)))))))

;;; GCD (Greatest Common Divisor)
;;; Implements Euclidean algorithm as described in McCarthy's paper
(define gcd-fn
  '(label gcd-fn
     (lambda (m n)
       (cond ((zero n) m)
             (t (gcd-fn n (remainder m n))))))

;;; Square root approximation using Newton's method
;;; As described in McCarthy's paper, section 3
(define sqrt-fn
  '(label sqrt-fn
     (lambda (a)
       ((label sqrt-iter
          (lambda (x)
            (cond ((good-enough? x) x)
                  (t (sqrt-iter (improve x))))))
        1.0))))

;;; Helper functions for sqrt approximation
(define good-enough?-fn
  '(lambda (x)
     (lessthan (abs (minus (square x) a)) 0.001)))

(define improve-fn
  '(lambda (x)
     (divide (plus x (divide a x)) 2)))

;; Add these to our environment
(define sqrt-env
  (append 
   `((good-enough? . ,good-enough?-fn)
     (improve . ,improve-fn))
   math-env))

;; Display usage examples
(display "McCarthy's mathematical functions from section 3:\n\n")

;; Factorial examples
(display "Factorial Examples:\n")
(let loop ((i 0))
  (if (< i 6)
      (begin
        (display i)
        (display "! = ")
        (display (apply factorial-fn (list i) math-env))
        (newline)
        (loop (+ i 1)))))

(newline)

;; GCD examples
(display "GCD Examples:\n")
(define gcd-examples '((48 18) (100 75) (35 49) (120 55)))
(for-each
 (lambda (pair)
   (let ((m (car pair))
         (n (cadr pair)))
     (display "gcd(")
     (display m)
     (display ", ")
     (display n)
     (display ") = ")
     (display (apply gcd-fn (list m n) math-env))
     (newline)))
 gcd-examples)

(newline)

;; Square root examples
(display "Square Root Examples:\n")
(define sqrt-examples '(2 4 9 16 25 100))
(for-each
 (lambda (num)
   (display "sqrt(")
   (display num)
   (display ") ≈ ")
   (display (apply sqrt-fn (list num) sqrt-env))
   (newline))
 sqrt-examples)

;; Also show native implementations
(display "\nComparison with native Scheme implementations:\n")
(display "Function         | McCarthy's Eval | Native Scheme\n")
(display "----------------+----------------+----------------\n")
(for-each
 (lambda (n)
   (let ((mccarthy-result (apply factorial-fn (list n) math-env))
         (native-result (factorial n)))
     (format #t "factorial(~a)     | ~12a | ~12a\n" n mccarthy-result native-result)))
 '(0 1 5 10))

(for-each
 (lambda (pair)
   (let ((m (car pair))
         (n (cadr pair))
         (mccarthy-result (apply gcd-fn (list (car pair) (cadr pair)) math-env))
         (native-result (gcd-recursive (car pair) (cadr pair))))
     (format #t "gcd(~a, ~a)    | ~12a | ~12a\n" m n mccarthy-result native-result)))
 '((48 18) (100 75)))

(for-each
 (lambda (n)
   (let ((mccarthy-result (apply sqrt-fn (list n) sqrt-env))
         (native-result (sqrt-approx n)))
     (format #t "sqrt(~a)         | ~12,5f | ~12,5f\n" n mccarthy-result native-result)))
 '(2 9 100))