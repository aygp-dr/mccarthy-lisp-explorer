;; test-core.scm - Tests for core-functions.scm
;;
;; This file tests the basic functions defined in core-functions.scm

(use-modules (ap mccarthy core-functions))

(display "Running core function tests...\n")
(newline)

;; Test atom?
(display "Testing atom?...\n")
(define atom-tests
  `(((atom? 'A) . #t)
    ((atom? '(A B)) . #f)
    ((atom? '()) . #f)))

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

(run-tests atom-tests)
(newline)

;; Test eq?
(display "Testing eq?...\n")
(define eq-tests
  `(((eq? 'A 'A) . #t)
    ((eq? 'A 'B) . #f)
    ((eq? '(A) 'A) . #f)))

(run-tests eq-tests)
(newline)

;; Test car and cdr
(display "Testing car and cdr...\n")
(define car-cdr-tests
  `(((car '(A B C)) . A)
    ((cdr '(A B C)) . (B C))
    ((car (cdr '(A B C))) . B)))

(run-tests car-cdr-tests)
(newline)

;; Test cons
(display "Testing cons...\n")
(define cons-tests
  `(((cons 'A '(B C)) . (A B C))
    ((cons 'A '()) . (A))
    ((cons '(A B) '(C D)) . ((A B) C D))))

(run-tests cons-tests)
(newline)

;; Test equal?
(display "Testing equal?...\n")
(define equal-tests
  `(((equal? '(A B C) '(A B C)) . #t)
    ((equal? '(A B C) '(A B D)) . #f)
    ((equal? 'A 'A) . #t)
    ((equal? '(A (B C)) '(A (B C))) . #t)))

(run-tests equal-tests)
(newline)

;; Test append
(display "Testing append...\n")
(define append-tests
  `(((append '(A B) '(C D)) . (A B C D))
    ((append '() '(C D)) . (C D))
    ((append '(A B) '()) . (A B))))

(run-tests append-tests)
(newline)

(display "All core tests completed.\n")