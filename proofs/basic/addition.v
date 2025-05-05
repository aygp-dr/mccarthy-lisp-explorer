(** Basic properties of addition on natural numbers *)

(** First, let's prove that 0 is a right identity for addition *)
Theorem plus_n_O : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.  (* Base case: 0 + 0 = 0 *)
  - simpl.        (* Inductive case: (S n') + 0 = S n' *)
    rewrite IHn'. (* Use induction hypothesis *)
    reflexivity.
Qed.

(** Now, let's prove that 0 is a left identity for addition *)
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.  (* This is trivial by definition of addition *)
Qed.

(** Let's prove the associativity of addition *)
Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - reflexivity.   (* Base case: 0 + (m + p) = (0 + m) + p *)
  - simpl.         (* Inductive case: S n' + (m + p) = (S n' + m) + p *)
    rewrite IHn'.  (* Use induction hypothesis *)
    reflexivity.
Qed.

(** Commutativity of addition requires a helper lemma *)
Lemma plus_n_Sm : forall n m : nat,
  n + S m = S (n + m).
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - reflexivity.  (* Base case: 0 + S m = S (0 + m) *)
  - simpl.        (* Inductive case: S n' + S m = S (S n' + m) *)
    rewrite IHn'. (* Use induction hypothesis *)
    reflexivity.
Qed.

(** Now we can prove commutativity *)
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - rewrite plus_O_n. (* Base case: 0 + m = m + 0 *)
    symmetry.
    apply plus_n_O.
  - simpl.            (* Inductive case: S n' + m = m + S n' *)
    rewrite IHn'.     (* Use induction hypothesis *)
    rewrite plus_n_Sm. (* Use helper lemma *)
    reflexivity.
Qed.
