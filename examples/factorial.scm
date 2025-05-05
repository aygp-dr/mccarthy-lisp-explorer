;;; factorial.scm -- Factorial implementation using McCarthy's approach
;;;
;;; Shows how to define and use recursive functions in McCarthy's LISP

(load "../src/evaluator.scm")

;; Define the factorial function using McCarthy's label construct
(define factorial-fn
  '(label factorial 
    (lambda (n) 
      (cond ((eq n 0) 1)
            (quote t) (times n (factorial (sub1 n)))))))

;; Initialize environment with basic math functions
(define math-env
  '((t . #t)
    (sub1 . ,(lambda (n) (- n 1)))
    (times . ,(lambda (x y) (* x y)))))

;; Compute factorials
(display "Factorial examples using McCarthy's evaluator:\n")
(newline)

;; Function to print factorials from 0 to n
(define (display-factorials n)
  (let loop ((i 0))
    (if (<= i n)
        (begin
          (display i)
          (display "! = ")
          (display (apply factorial-fn (list i) math-env))
          (newline)
          (loop (+ i 1))))))

(display-factorials 10)

;; Demonstrate how computation happens
(display "\nStep-by-step application of factorial 3:\n")
(display "1. Apply factorial-fn to 3\n")
(display "2. Eval (cond ((eq n 0) 1) (quote t) (times n (factorial (sub1 n))))\n")
(display "3. n = 3, so eq returns false\n")
(display "4. Next condition 't' is true\n")
(display "5. Eval (times 3 (factorial (sub1 3)))\n")
(display "6. sub1 returns 2\n")
(display "7. Recursive call factorial with 2\n")
(display "8. Similar process repeats until base case\n")
(display "9. Result: 3 * 2 * 1 = 6\n")
