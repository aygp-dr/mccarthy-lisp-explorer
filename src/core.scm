;;; core.scm -- Core functions from McCarthy's paper
;;;
;;; Implementation of McCarthy's higher-level Lisp functions

(load "./s-expressions.scm")

;; Define McCarthy's label, lambda and conditional functions

;; ff (find function) - used to lookup values in association lists
;; Similar to what McCarthy calls "assoc" in section 3
(define (ff x a)
  (cond ((null? a) #f)
        ((mccarthy-eq? x (mccarthy-car (mccarthy-car a)))
         (mccarthy-car (mccarthy-cdr (mccarthy-car a))))
        (else (ff x (mccarthy-cdr a)))))

;; Substitution function (based on section 3's "subst")
;; Replaces variables in expression e according to values in a
(define (sublis a e)
  (cond ((mccarthy-atom? e) (or (ff e a) e))
        (else (mccarthy-cons (sublis a (mccarthy-car e))
                            (sublis a (mccarthy-cdr e))))))

;; Implementation of McCarthy's LISP "null" predicate
(define (mccarthy-null? x)
  (eq? x '()))

;; Equal predicate for S-expressions (section 3)
(define (mccarthy-equal? x y)
  (cond ((and (mccarthy-atom? x) (mccarthy-atom? y))
         (mccarthy-eq? x y))
        ((or (mccarthy-atom? x) (mccarthy-atom? y))
         #f)
        ((mccarthy-equal? (mccarthy-car x) (mccarthy-car y))
         (mccarthy-equal? (mccarthy-cdr x) (mccarthy-cdr y)))
        (else #f)))

;; The "append" function from McCarthy's paper
(define (mccarthy-append x y)
  (cond ((mccarthy-null? x) y)
        (else (mccarthy-cons (mccarthy-car x) 
                           (mccarthy-append (mccarthy-cdr x) y)))))

;; McCarthy's pair implementation (section 3)
(define (mccarthy-pair x y)
  (cond ((and (mccarthy-null? x) (mccarthy-null? y)) '())
        ((and (not (mccarthy-atom? x))
              (not (mccarthy-atom? y))
              (not (mccarthy-null? x))
              (not (mccarthy-null? y)))
         (mccarthy-cons (mccarthy-list (mccarthy-car x) (mccarthy-car y))
                       (mccarthy-pair (mccarthy-cdr x) (mccarthy-cdr y))))
        (else (error "pair: arguments must be lists of equal length"))))

;; Assoc function from section 3
(define (mccarthy-assoc x a)
  (cond ((mccarthy-eq? (mccarthy-car (mccarthy-car a)) x) (mccarthy-car a))
        (else (mccarthy-assoc x (mccarthy-cdr a)))))

;; Test our core functions
(define test-ff (ff 'x '((x . 1) (y . 2))))                      ;; 1
(define test-sublis (sublis '((x . a) (y . b)) '(x y z)))        ;; (a b z)
(define test-null (mccarthy-null? '()))                          ;; #t
(define test-equal (mccarthy-equal? '(a b c) '(a b c)))          ;; #t
(define test-append (mccarthy-append '(a b) '(c d)))             ;; (a b c d)
(define test-pair (mccarthy-pair '(a b c) '(1 2 3)))             ;; ((a 1) (b 2) (c 3))
