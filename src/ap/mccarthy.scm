;; mccarthy.scm - Main module for McCarthy's Lisp exploration
;;
;; Re-exports all components from the McCarthy Lisp explorer

(define-module (ap mccarthy)
  #:use-module (ap mccarthy core-functions)
  #:use-module (ap mccarthy evaluator)
  #:re-export (
    ;; From core-functions
    atom? eq? car cdr cons
    null? equal? append pair assoc list
    apply-to-all subst member
    factorial gcd-recursive sqrt-approx
    trace-on trace-off
    
    ;; From evaluator
    eval apply evlis evcon
    make-env extend-env lookup-var
  ))

;; Display a welcome message
(define (display-welcome)
  (display "\nMcCarthy's LISP Explorer\n")
  (display "======================\n\n")
  (display "This module provides an implementation of concepts from McCarthy's 1960 paper\n")
  (display "\"Recursive Functions of Symbolic Expressions and Their Computation by Machine, Part I\"\n\n")
  (display "Basic primitives: atom?, eq?, car, cdr, cons\n")
  (display "Core functions: null?, equal?, append, pair, assoc, apply-to-all, subst, member\n")
  (display "Mathematical functions: factorial, gcd-recursive, sqrt-approx\n")
  (display "Evaluator: eval, apply, evlis, evcon, make-env, extend-env, lookup-var\n\n")
  (display "Examples can be found in the examples/ directory.\n")
  (display "Try running (trace-on) before using the functions to see tracing information.\n\n"))

;; Display welcome message when the module is used directly
(if (equal? (current-module) (resolve-module '(ap mccarthy)))
    (display-welcome))