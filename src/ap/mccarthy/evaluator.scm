;; evaluator.scm - McCarthy's Lisp evaluator
;;
;; This file implements McCarthy's universal evaluator as described
;; in his 1960 paper, section 4.

(define-module (ap mccarthy evaluator)
  #:use-module (ap mccarthy core-functions)
  #:export (eval apply evlis evcon 
            make-env extend-env lookup-var))

;; Our environment will contain primitive functions
(define primitive-functions
  `((car . ,car)
    (cdr . ,cdr)
    (cons . ,cons)
    (atom . ,atom?)
    (eq . ,eq?)
    (null . ,null?)
    (equal . ,equal?)
    (append . ,append)
    (subst . ,subst)
    (member . ,member)
    (apply-to-all . ,apply-to-all)
    (assoc . ,assoc)
    (+ . ,+)
    (- . ,-)
    (* . ,*)
    (/ . ,/)
    (< . ,<)
    (> . ,>)
    (= . ,=)))

;; ff (find function) - lookup values in an association list
(define (ff x a)
  (cond ((null? a) #f)
        ((eq? x (car (car a)))
         (car (cdr (car a))))
        (else (ff x (cdr a)))))

;; evlis - evaluates a list of expressions (section 4)
(define (evlis m a)
  (cond ((null? m) '())
        (else (cons (eval (car m) a)
                    (evlis (cdr m) a)))))

;; evcon - evaluates a list of conditional expressions (section 4)
(define (evcon c a)
  (cond ((eval (car (car c)) a)
         (eval (car (cdr (car c))) a))
        (else (evcon (cdr c) a))))

;; apply - applies a function to arguments (section 4)
(define (apply fn args a)
  (cond 
    ;; Primitive function
    ((atom? fn)
     (let ((primitive (assoc fn primitive-functions)))
       (if primitive
           (apply-primitive (cdr primitive) args)
           (apply (ff fn a) args a))))
    
    ;; Lambda expression
    ((eq? (car fn) 'lambda)
     (eval (car (cdr (cdr fn)))
           (append (pair (car (cdr fn)) args) a)))
    
    ;; Label (recursive function)
    ((eq? (car fn) 'label)
     (apply (car (cdr (cdr fn)))
            args
            (cons (list (car (cdr fn)) 
                      (car (cdr (cdr fn))))
                 a)))))

;; Apply primitive function - helper for built-in functions
(define (apply-primitive fn args)
  (apply fn args))

;; Environment helpers

;; make-env: Creates a new environment with primitive bindings
(define (make-env)
  primitive-functions)

;; extend-env: Adds new bindings to an environment
(define (extend-env bindings env)
  (append bindings env))

;; lookup-var: Looks up a variable in an environment
(define (lookup-var var env)
  (ff var env))

;; eval - evaluates an expression in an environment (section 4)
(define (eval expr a)
  (cond 
    ;; Atomic symbol - lookup in environment
    ((atom? expr) (ff expr a))
    
    ;; Atomic function application
    ((atom? (car expr))
     (cond 
       ;; Quote - return argument unevaluated
       ((eq? (car expr) 'quote)
        (car (cdr expr)))
       
       ;; Cond - evaluate conditional
       ((eq? (car expr) 'cond)
        (evcon (cdr expr) a))
       
       ;; Define (extension for convenience)
       ((eq? (car expr) 'define)
        (let ((var (car (cdr expr)))
              (val (eval (car (cdr (cdr expr))) a)))
          (set! a (cons (list var val) a))
          var))
       
       ;; Let (extension for convenience)
       ((eq? (car expr) 'let)
        (let* ((bindings (car (cdr expr)))
               (body (car (cdr (cdr expr))))
               (vars (apply-to-all car bindings))
               (vals (apply-to-all 
                       (lambda (b) (eval (car (cdr b)) a))
                       bindings))
               (new-env (extend-env (pair vars vals) a)))
          (eval body new-env)))
       
       ;; Function application
       (else (apply (car expr)
                   (evlis (cdr expr) a)
                   a))))
    
    ;; Non-atomic function application (e.g., lambda or label)
    (else (apply (car expr)
                (evlis (cdr expr) a)
                a))))