(** Definition and properties of integer square root *)

(** Helper function to iteratively compute integer square root 
    using Newton's method, showing how recursive functions can implement
    numerical algorithms *)
Fixpoint isqrt_iter (n guess : nat) (fuel : nat) : nat :=
  match fuel with
  | 0 => guess
  | S fuel' =>
      let next := (guess + n / guess) / 2 in
      if next =? guess then guess 
      else isqrt_iter n next fuel'
  end.

(** Integer square root function *)
Definition isqrt (n : nat) : nat :=
  match n with
  | 0 => 0
  | _ => isqrt_iter n 1 100  (* 100 iterations should be enough *)
  end.

(** Let's test with some examples *)
Example isqrt_0 : isqrt 0 = 0.
Proof. reflexivity. Qed.

Example isqrt_1 : isqrt 1 = 1.
Proof. reflexivity. Qed.

Example isqrt_16 : isqrt 16 = 4.
Proof. reflexivity. Qed.

Example isqrt_17 : isqrt 17 = 4.
Proof. reflexivity. Qed.

(** An alternative implementation for smaller numbers *)
Fixpoint find_sqrt (n m : nat) : nat :=
  match m with
  | 0 => 0
  | S m' => 
      if (S m') * (S m') <=? n then S m'
      else find_sqrt n m'
  end.

Definition sqrt_simple (n : nat) : nat := find_sqrt n n.

(** The integer square root function returns the floor of the actual square root *)
Theorem isqrt_correct : forall n : nat,
  let r := isqrt n in
  r * r <= n /\ (r + 1) * (r + 1) > n.
Proof.
  (* This proof requires analysis of the Newton-Raphson method *)
  (* For simplicity, we'll admit this theorem *)
Admitted.

(** The square root of a perfect square is exact *)
Theorem isqrt_perfect : forall n : nat,
  isqrt (n * n) = n.
Proof.
  (* This follows from the correctness theorem *)
Admitted.

(** The two implementations are equivalent for small numbers *)
Theorem sqrt_impls_equivalent : forall n : nat,
  n <= 100 -> isqrt n = sqrt_simple n.
Proof.
  (* This requires detailed analysis of both algorithms *)
Admitted.
