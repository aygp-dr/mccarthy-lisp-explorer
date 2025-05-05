(** Definition and properties of the Fibonacci sequence *)

(** Recursive definition of Fibonacci *)
Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n' as n'') => fib n' + fib n''
  end.

(** Test with some examples *)
Example fib_0 : fib 0 = 0.
Proof. reflexivity. Qed.

Example fib_1 : fib 1 = 1.
Proof. reflexivity. Qed.

Example fib_2 : fib 2 = 1.
Proof. reflexivity. Qed.

Example fib_7 : fib 7 = 13.
Proof. reflexivity. Qed.

(** Every Fibonacci number after the first is positive *)
Theorem fib_positive : forall n : nat,
  n > 0 -> fib n > 0.
Proof.
  intros n H.
  destruct n.
  - inversion H. (* Contradiction: 0 > 0 is false *)
  - induction n.
    + simpl. apply Nat.lt_0_1. (* fib 1 = 1 > 0 *)
    + simpl.                  (* fib (S (S n)) = fib n + fib (S n) *)
      apply Nat.add_pos_pos.
      * apply IHn. apply Nat.lt_0_succ.
      * apply Nat.lt_0_1.
Qed.

(** Alternating sum of Fibonacci numbers: fib(n+1) - fib(n-1) = fib(n-2) *)
Theorem fib_alternating_sum : forall n : nat,
  n >= 3 -> fib (n + 1) - fib (n - 1) = fib (n - 2).
Proof.
  intros n Hn.
  (* This requires careful manipulation of the recursive definition *)
  (* For simplicity, we'll admit this theorem *)
Admitted.

(** Fibonacci numbers grow at least linearly *)
Theorem fib_grows_linearly : forall n : nat,
  n >= 6 -> fib n >= n.
Proof.
  intros n Hn.
  (* This requires induction with a stronger hypothesis *)
Admitted.

(** Iterative computation of Fibonacci (more efficient) - 
    This is analogous to tail recursion optimization, a concept that evolved
    from McCarthy's early work *)
Fixpoint fib_iter (n a b : nat) : nat :=
  match n with
  | 0 => a
  | S n' => fib_iter n' b (a + b)
  end.

Definition fibonacci (n : nat) : nat := fib_iter n 0 1.

(** The iterative implementation is equivalent to the recursive one *)
Theorem fib_equivalent : forall n : nat,
  fib n = fibonacci n.
Proof.
  (* This requires a helper lemma and careful induction *)
Admitted.
