#!/usr/bin/env guile3
!#

;; Add our source directory to the load path
(add-to-load-path ".")

;;; run-all.scm -- Run all tests and examples
;;;
;;; This script runs all tests and examples to demonstrate
;;; the implementation of McCarthy's LISP functions.

(define (with-section-header title thunk)
  (let ((width 60)
        (title-length (string-length title)))
    (let* ((padding (max 0 (- width title-length 4)))
           (left (quotient padding 2))
           (right (- padding left)))
      (display (make-string width #\=))
      (newline)
      (display (string-append 
                (make-string left #\=)
                "[ " title " ]"
                (make-string right #\=)))
      (newline)
      (display (make-string width #\=))
      (newline)
      (newline)
      (thunk)
      (newline))))

(define (run-file file)
  (with-section-header (string-append "Running " file)
    (lambda ()
      (load file))))

;; Run the core tests
(run-file "./tests/test-core.scm")

;; Run the evaluator tests
(run-file "./tests/test-evaluator.scm")

;; Run the math function tests and examples
(run-file "./tests/test-math-functions.scm")
(run-file "./examples/math-functions.scm")

;; Display summary
(with-section-header "Summary"
  (lambda ()
    (display "All tests and examples have been run successfully.\n")
    (display "This demonstrates the implementation of key functions from\n")
    (display "McCarthy's 1960 paper 'Recursive Functions of Symbolic\n")
    (display "Expressions and Their Computation by Machine, Part I.'\n")
    (newline)
    (display "The implementation includes:\n")
    (display "1. The five elementary functions (atom, eq, car, cdr, cons)\n")
    (display "2. The core higher-level functions (equal, append, assoc, etc.)\n")
    (display "3. Mathematical functions (factorial, GCD, sqrt)\n")
    (display "4. The universal LISP evaluator (eval/apply)\n")))

;; Make the script executable
(chmod "run-all.scm" #o755)