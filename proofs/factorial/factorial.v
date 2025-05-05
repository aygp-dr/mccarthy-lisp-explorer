(** Definition and properties of the factorial function *)

(** Recursive definition of factorial *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => n * factorial n'
  end.

(** Let's compute some examples *)
Example factorial_0 : factorial 0 = 1.
Proof. reflexivity. Qed.

Example factorial_1 : factorial 1 = 1.
Proof. reflexivity. Qed.

Example factorial_5 : factorial 5 = 120.
Proof. reflexivity. Qed.

(** Factorial is always positive *)
Theorem factorial_positive : forall n : nat,
  factorial n > 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. apply le_n.  (* factorial 0 = 1 > 0 *)
  - simpl.              (* factorial (S n') = (S n') * factorial n' *)
    apply Nat.mul_pos_pos.
    + apply Nat.lt_0_succ. (* S n' > 0 *)
    + exact IHn'.         (* factorial n' > 0 by induction *)
Qed.

(** Relation between successive factorials *)
Theorem factorial_succ : forall n : nat,
  factorial (S n) = (S n) * factorial n.
Proof.
  intros n.
  simpl. (* This follows directly from the definition *)
  reflexivity.
Qed.

(** Alternative definition of factorial using recursion equation - 
    This style is closer to McCarthy's approach in defining recursive functions *)
Definition factorial_rec (n : nat) : nat :=
  if n =? 0 then 1 else n * factorial_rec (n - 1).

(** The two definitions are equivalent *)
Theorem factorial_equivalent : forall n : nat,
  factorial n = factorial_rec n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite Nat.sub_0_r.
    rewrite Nat.eqb_refl.
    reflexivity.
Qed.
