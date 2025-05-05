;; test-evaluator.scm - Tests for evaluator.scm
;;
;; Tests McCarthy's universal evaluator

(add-to-load-path "..")

(use-modules (ap mccarthy core-functions)
             (ap mccarthy evaluator))

(display "Running evaluator tests...\n")
(newline)

;; Test eval for quote
(display "Testing quote expressions...\n")
(define quote-tests
  '(((eval '(quote A) '()) . A)
    ((eval '(quote (A B C)) '()) . (A B C))))

(define (run-tests tests)
  (let ((failures '()))
    (for-each
     (lambda (test)
       (let* ((expr (car test))
              (expected (cdr test))
              (result (eval expr (interaction-environment))))
         (if (equal? result expected)
             (begin
               (display "PASS: ")
               (display expr)
               (newline))
             (begin
               (display "FAIL: ")
               (display expr)
               (display " expected ")
               (display expected)
               (display " but got ")
               (display result)
               (newline)
               (set! failures (cons expr failures))))))
     tests)
    failures))

(run-tests quote-tests)
(newline)

;; Test eval for car, cdr, cons
(display "Testing basic function evaluation...\n")
(define basic-fn-tests
  '(((eval '(car (quote (A B C))) '()) . A)
    ((eval '(cdr (quote (A B C))) '()) . (B C))
    ((eval '(cons (quote A) (quote (B C))) '()) . (A B C))))

(run-tests basic-fn-tests)
(newline)

;; Test eval for cond
(display "Testing cond expressions...\n")
(define cond-tests
  '(((eval '(cond ((atom? (quote A)) (quote atom))
                  (t (quote not-atom)))
          '((t . #t))) 
     . atom)
    ((eval '(cond ((atom? (quote (A))) (quote atom))
                  (t (quote not-atom)))
          '((t . #t))) 
     . not-atom)))

(run-tests cond-tests)
(newline)

;; Test lambda expressions
(display "Testing lambda expressions...\n")
(define env '((x . 1) (y . 2) (t . #t)))

(define lambda-tests
  (list 
   (cons '(eval '((lambda (z) (cons z (quote (b)))) (quote a)) env)
         '(a b))
   (cons '(eval '((lambda (x) (cons x (quote (b)))) (quote a)) env)
         '(a b))))

(run-tests lambda-tests)
(newline)

;; Test label (recursive functions)
(display "Testing recursive functions with label...\n")
(define math-env
  '((t . #t)
    (sub1 . ,(lambda (n) (- n 1)))
    (add1 . ,(lambda (n) (+ n 1)))
    (plus . ,(lambda (x y) (+ x y)))
    (times . ,(lambda (x y) (* x y)))
    (zero . ,(lambda (x) (= x 0)))))

(define factorial-fn
  '(label factorial 
    (lambda (n) 
      (cond ((zero n) 1)
            (t (times n (factorial (sub1 n)))))))

;; Test factorial of 5
(define fact-result 
  (apply factorial-fn '(5) math-env))

(display "Factorial of 5: ")
(display fact-result)
(if (= fact-result 120)
    (display " ✓")
    (display " ✗"))
(newline)
(newline)

(display "All evaluator tests completed.\n")