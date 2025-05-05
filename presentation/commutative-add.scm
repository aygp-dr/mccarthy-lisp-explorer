;; Addition is built-in, but we can define commutative-add
(define (commutative-add a b)
  (if (= a 0)
      b
      (commutative-add (- a 1) (+ b 1))))
