(**********************************************************************)
(*  This is part of base_pc, it is distributed under the terms of the *)
(*          GNU Lesser General Public License version 3               *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2023-2028                            *)
(*       Dakai Guo, qiming Wang, jianghao Liu and Wensheng Yu         *)
(**********************************************************************)

(** base_pc *)

Require Export Coq.Sets.Ensembles.

Notation "a ∈ A" := (In _ A a) (at level 10).
Notation "B ∪ C" := (Union _ B C) (at level 65, left associativity).
Notation "[ a ]" := (Singleton _ a) (at level 0, right associativity).
Notation "A ⊆ B" := (Included _ A B) (at level 70).

Corollary UnionI : forall {U} (a: U) B C, a ∈ (B ∪ C) <-> a ∈ B \/ a ∈ C.
Proof. split; intros; destruct H; eauto with sets. Qed.

Corollary Single : forall {U} (a x: U), a ∈ [ x ] <-> a = x.
Proof. split; intros. destruct H; auto. rewrite H. split. Qed.

Global Hint Resolve UnionI Single: sets.

(*Inductive Formula : Type:=
  | X : nat -> Formula
  | Not : Formula -> Formula
  | Contain : Formula -> Formula -> Formula.

Notation "¬ q" := (Not q)(at level 5,right associativity).
Notation "p → q" := (Contain p q)(at level 8,right associativity).*)
