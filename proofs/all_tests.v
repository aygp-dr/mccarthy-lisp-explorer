(** Tests for all our implementations *)

(* Import our modules *)
From McCarthyLispProofs.basic Require Import addition.
From McCarthyLispProofs.factorial Require Import factorial.
From McCarthyLispProofs.gcd Require Import gcd.
From McCarthyLispProofs.fibonacci Require Import fibonacci.
From McCarthyLispProofs.sqrt Require Import sqrt.
From McCarthyLispProofs.lambda Require Import lambda_basics y_combinator.

(** Addition tests *)
Example addition_test_1 : 3 + 5 = 8.
Proof. reflexivity. Qed.

Example addition_test_2 : 0 + 42 = 42.
Proof. apply plus_O_n. Qed.

Example addition_test_3 : 42 + 0 = 42.
Proof. apply plus_n_O. Qed.

Example addition_test_4 : 2 + 3 = 3 + 2.
Proof. apply plus_comm. Qed.

(** Factorial tests *)
Example factorial_test_1 : factorial 4 = 24.
Proof. reflexivity. Qed.

Example factorial_test_2 : factorial 6 = 720.
Proof. reflexivity. Qed.

(** GCD tests *)
Example gcd_test_1 : gcd 48 18 = 6.
Proof. reflexivity. Qed.

Example gcd_test_2 : gcd 35 49 = 7.
Proof. reflexivity. Qed.

Example gcd_test_3 : gcd 35 36 = 1.
Proof. reflexivity. Qed.

(** Fibonacci tests *)
Example fib_test_1 : fib 10 = 55.
Proof. reflexivity. Qed.

Example fib_test_2 : fibonacci 10 = 55.
Proof. 
  (* Requires our equivalence theorem *)
  (* For now, compute directly *)
  unfold fibonacci. simpl. reflexivity.
Qed.

(** Square root tests *)
Example sqrt_test_1 : isqrt 25 = 5.
Proof. reflexivity. Qed.

Example sqrt_test_2 : isqrt 26 = 5.
Proof. reflexivity. Qed.

Example sqrt_test_3 : isqrt 24 = 4.
Proof. reflexivity. Qed.

(** Combined examples *)
Example combined_1 : factorial (isqrt 25) = 120.
Proof. reflexivity. Qed.

Example combined_2 : gcd (fib 7) (factorial 3) = 1.
Proof. reflexivity. Qed.

(** 
 * These examples demonstrate formal verification of algorithms
 * that share computational patterns with McCarthy's Lisp functions.
 * The recursive definitions and pattern matching are particularly
 * relevant to understanding McCarthy's contributions to computer science.
 *)
