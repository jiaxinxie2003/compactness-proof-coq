(************************************************************************)
(*  This is part of syntax_pc, it is distributed under the terms of the *)
(*           GNU Lesser General Public License version 3                *)
(*              (see file LICENSE for more details)                     *)
(*                                                                      *)
(*                      Copyright 2023-2028                             *)
(*        Dakai Guo, qiming Wang, jianghao Liu and Wensheng Yu          *)
(************************************************************************)

(** syntax_K_System *)

Require Import base_pc.
Require Import formulas_K_System.

Section Predicate_Calculus.

(* 公理系统 *)
Inductive Axiom_system : Formula -> Prop :=
  | P1 : forall p q, Axiom_system (p → (q → p))
  | P2 : forall p q r, Axiom_system ((p → (q → r)) → ((p → q) → (p → r)))
  | P3 : forall p q, Axiom_system ((¬p → q) → ((¬p → ¬q) → p))
  | S' : forall p x t, t_x_free p t x = true 
           -> Axiom_system ((∀ x , p) → (substitute_f p t x))
  | D' : forall p x q, Axiom_system ((∀ x, (p → q)) → (∀ x, p) → (∀ x, q)) 
  | E1 : forall t, Axiom_system (equality t t)
  | E2 : forall t1 t2, Axiom_system ((equality t1 t2) → (equality t2 t1))
  | E3 : forall t1 t2 t3, Axiom_system 
           ((equality t1 t2) → (equality t2 t3) → (equality t1 t3))
  | E4 : forall r v1 v2, Axiom_system 
           (equality_4 (( atomic r v1) → (atomic r v2)) _ _ v1 v2)
  | E5 : forall f v1 v2, Axiom_system 
           (equality_4 (equality (Tfun f v1) (Tfun f v2)) _ _ v1 v2)
  | C1 : forall x p, ~(x ∈ (Formula_free_Ens p)) -> Axiom_system (p → (∀ x, p))
  | C2 : forall x p, Axiom_system p -> Axiom_system (∀ x, p).

(* 证明与演绎 *)
Inductive deduce_K (Γ: Ensemble Formula) : Formula -> Prop :=
  | K0 : forall p, p ∈ Γ -> deduce_K Γ p
  | K1 : forall p, Axiom_system p -> deduce_K Γ p
  | MP : forall p q, deduce_K Γ (p → q) -> deduce_K Γ p -> deduce_K Γ q.

End Predicate_Calculus.

(* 语法蕴涵 *)
Notation " ├ p " := (deduce_K (@ Φ) p) (at level 80).
Notation " Γ ├ p " := (deduce_K Γ p) (at level 80).
Global Hint Constructors Axiom_system deduce_K : KD.


Fact Union_l : forall Γ p, Γ ├ p -> forall A, Γ ∪ A ├ p.
Proof. intros. induction H; eauto with KD sets. Qed.

Fact Union_r : forall Γ p, Γ ├ p -> forall A, A ∪ Γ ├ p.
Proof. intros. induction H; eauto with KD sets. Qed.

Fact Union_r_A : forall A p, A ├ p -> forall Γ, Γ ∪ A ├ p.
Proof. intros. induction H; eauto with KD sets. Qed.

Fact Union_l_A : forall A p, A ├ p -> forall Γ, A ∪ Γ ├ p.
Proof. intros. induction H; eauto with KD sets. Qed.

Fact subsetprove : forall A B p, A ⊆ B -> A ├ p -> B ├ p.
Proof. (*易证*) 
  intros A B p H H0. induction H0.
  - apply K0. apply H. auto.
  - apply K1. auto.
  - eapply MP; eauto.
Qed.

Ltac autoK :=
  match goal with
  | H: ?Γ ├ ?p |- ?Γ ∪ ?A ├ ?p => apply Union_l; auto
  | H: ?Γ ├ ?p |- ?A ∪ ?Γ ├ ?p => apply Union_r; auto
  | H: ?a ∈ Φ |- _ => destruct H
  | H: ?Γ ├ ?p , H1: ?Γ ├ ?p → ?q |- ?Γ ├ ?q => apply MP with p; autoK
  | H: ?Γ ├ ?p |- ?Γ ├ ?q → ?p => let H0 := fresh in
      assert (H0: Γ ├ p → (q → p)) by (apply K1; apply P1; constructor); autoK
  | H1: ?Γ ├ ¬?p  → ¬?q, H2: ?Γ ├ ¬?p  → ?q |- ?Γ ├ ?p =>
      assert (H0: Γ ├ (¬p → q) → ((¬p → ¬q) → p)) by 
        (apply K1; apply P3; constructor); autoK
  | |- ?Γ ├ ?x => eauto with KD sets
  | |- forall a, ?Q => intros; autoK
  end.

Ltac Single_Union :=
  match goal with 
  | |- ?Γ ∪ [?p] ├ ?q => assert(Γ ∪ [p] ├ p); autoK
  end.

Ltac later :=
  match goal with
  | |- ?Γ ├ ?q → ?p => let H0 := fresh in assert (H0: Γ ├ p) by (autoK); autoK
  end.


(* 同一律 |- p→q *)
Proposition law_identity : forall Γ p, Γ ├ p → p.
Proof. intros. assert(Γ ├ p → (p → p) → p) by autoK. autoK. Qed.
Global Hint Resolve law_identity : KD.


(* 演绎定理  *)
Theorem Deductive_Theorem : forall Γ p q, Γ ∪ [p] ├ q <-> Γ ├ p → q.
Proof.
  split; intros.
  - induction H; try (autoK; ES).
    + assert (Γ ├ p0 → p → p0); autoK.
    + destruct H; autoK.  
  - apply MP with p; autoK.
Qed.

Corollary syllogism : forall Γ p q r, Γ ∪ [p] ├ q -> Γ ∪ [q] ├ r -> Γ ∪ [p] ├ r.
Proof.
  intros. apply Deductive_Theorem in H. apply Deductive_Theorem in H0. 
  assert (Γ ∪ [p] ├ p) by autoK. pose proof (Union_l _ _ H [p]). 
  pose proof (Union_l _ _ H0 [p]). autoK.
Qed.

Corollary Syllogism : forall Γ p q r, Γ ├ (p → q) → (q → r) → (p → r).
Proof.
  intros. apply Deductive_Theorem. repeat apply -> Deductive_Theorem.
  assert (Γ ∪ [p → q] ∪ [q → r] ∪ [p] ├ p). 
    { apply Union_r_A. pose proof (K0 [p] p). apply H. apply In_singleton. }
  assert (Γ ∪ [p → q] ∪ [q → r] ∪ [p] ├ p → q).
    { apply Union_l_A. apply Union_l_A. apply Union_r_A. 
      pose proof (K0 [p → q] (p → q)). apply H0. apply In_singleton. }
  pose proof (MP _ _ _ H0 H).
  assert (Γ ∪ [p → q] ∪ [q → r] ∪ [p] ├ q → r).
    { apply Union_l_A. repeat apply Union_r_A. pose proof (K0 [q → r] (q → r)).
      apply H2. apply In_singleton. }
  pose proof (MP _ _ _ H2 H1). apply H3.
Qed.


(* 反证律 *)
Theorem rule_Indirect : forall Γ p q, Γ ∪ [¬p] ├ q ->  Γ ∪ [¬p] ├ ¬q -> Γ ├ p.
Proof. intros. apply Deductive_Theorem in H0, H. autoK. Qed.

(* 推论 双重否定律 *)
Corollary law_double_negation_aux : forall p, [¬¬p] ├ p.
Proof. intros. pose proof (rule_Indirect [¬¬p] p ¬p). apply H; autoK. Qed.

Global Hint Resolve law_double_negation_aux :KD.

Corollary law_double_negation : forall  Γ p, Γ ├ ¬¬p → p.
Proof. intros; apply Deductive_Theorem. apply Union_r_A. autoK. Qed.

Global Hint Resolve law_double_negation : KD.

(* 归谬律 law of reduction to absurdity *)
Theorem rule_Reduction_absurdity :
  forall Γ p q, Γ ∪ [p] ├ q -> Γ ∪ [p] ├ ¬q -> Γ ├ ¬p.
Proof.
  intros. assert (Γ ∪ [¬¬p] ├ q). { eapply (syllogism Γ (¬¬p) p q); autoK. } 
  assert (Γ ∪ [¬¬p] ├ ¬q). { eapply (syllogism Γ (¬¬p) p (¬q)); autoK. }
  apply (rule_Indirect _ _ _ H1 H2); auto.
Qed.

(* 第二双重否定律 *)
Corollary law_double_negation_second_aux : forall  p, [p] ├ ¬¬p.
Proof.
  intros. pose proof (rule_Reduction_absurdity [p] ¬p p). apply H; autoK.
Qed.

Corollary law_double_negation_second : forall Γ p , Γ ├ p → ¬¬p.
Proof.
  intros. pose proof (law_double_negation_second_aux p).
  assert (Γ ∪ [p] ├ ¬¬p). { apply Union_r_A. auto. }
  apply Deductive_Theorem in H0. auto.
Qed.

Global Hint Resolve law_double_negation_second : KD.


(* L3 |- (¬p → ¬q) → (q → p) *)
Fact L3 : forall Γ p q, Γ ├ ((¬p → ¬q) → (q → p)).
Proof.
  intros. apply Deductive_Theorem. apply -> Deductive_Theorem.
  apply rule_Indirect with q. eauto with *. apply MP with ¬p.
  eauto with *. eauto with *.
Qed.


(* 否定前件律 *)
Proposition law_deny_antecedent : forall Γ p q, Γ ├ ¬q → (q → p).
Proof.
  intros. assert (Γ ├ (¬p → ¬q) → (q → p)). { pose proof (L3 Γ p q). apply H. }
  assert (Γ ├ ((¬p → ¬q) → (q → p))→ (¬q → ((¬p → ¬q) → (q → p)))).
    { pose proof (P1 ((¬p → ¬q) → (q → p)) ¬q). apply K1. apply H0. }
  pose proof (MP _ _ _ H0 H).
  assert (Γ ├ (¬q → (¬p → ¬q) → (q → p)) → ((¬q → (¬p → ¬q)) → (¬q → (q → p)))).
    { pose proof (P2 ¬q (¬p → ¬q) (q → p)). apply K1. apply H2. }
  pose proof (MP _ _ _ H2 H1).
  assert (Γ ├ ¬q → (¬p → ¬q)). { pose proof (P1 ¬q ¬p). apply K1. apply H4. }
  pose proof (MP _ _ _ H3 H4). apply H5.
Qed.

Global Hint Resolve law_deny_antecedent : KD.

Definition Contradiciton Γ := exists q, Γ ├ q /\ Γ ├ ¬q.

Definition No_Contradiciton Γ := forall q, ~ (Γ ├ q /\ Γ ├ ¬q).

Proposition prop_3_3 : forall Γ, Contradiciton Γ ->  forall p, Γ ├ p.
Proof. intros; destruct H, H; autoK. Qed.

(* 否定肯定律 *)
Proposition law_negetion_affirmation : forall Γ p, Γ ├ (¬p → p) → p.
Proof.
  intros. apply Deductive_Theorem. set (Γ ∪ [¬p → p]) as A.
  pose proof (law_deny_antecedent A ¬(¬p → p) p).
  assert (A ├ (¬p → p → ¬(¬p → p)) → (¬p → p) → ¬p → ¬(¬p → p)).
    { pose proof (P2 ¬p p ¬(¬p → p)). apply K1. apply H0. }
  pose proof (MP _ _ _ H0 H).
  assert ( A ├ (¬p → p)). { apply Union_r_A. pose proof (K0 [¬p → p] (¬p → p)).
    apply H2. apply In_singleton. }
  pose proof (MP _ _ _ H1 H2).
  assert ( A ├ (¬p → ¬(¬p → p)) → (¬p → p) → p). 
    { pose proof (L3 A p (¬p → p)). apply H4. }
  pose proof (MP _ _ _ H4 H3). pose proof (MP _ _ _ H5 H2). apply H6.
Qed.

Global Hint Resolve law_negetion_affirmation : KD.


(* 换位律 *)
Fact law_inverse_prop : forall Γ p q, Γ ├ (q → p) → (¬p → ¬q).
Proof.
  intros. apply Deductive_Theorem. assert (Γ ∪ [q → p] ├ ¬¬q → q) by autoK.
  pose proof (K0 (Γ ∪ [q → p]) (q → p)). assert ((q → p) ∈ (Γ ∪ [q → p])) by ES.
  apply H0 in H1. pose proof (Syllogism (Γ ∪ [q → p]) ¬¬q q p).
  pose proof (MP _ _ _ H2 H). pose proof (MP _ _ _ H3 H1).
  assert (Γ ∪ [q → p] ├ p → ¬¬p). { apply law_double_negation_second. }
  pose proof (Syllogism (Γ ∪ [q → p]) ¬¬q p ¬¬p).
  pose proof (MP _ _ _ H6 H4). pose proof (MP _ _ _ H7 H5).
  assert (Γ ∪ [q → p] ├ (¬¬q → ¬¬p) → ¬p → ¬q).
  { pose proof (L3 (Γ ∪ [q → p]) ¬q ¬p). auto. }
  pose proof (MP _ _ _ H9 H8). auto.
Qed.

Global Hint Resolve law_inverse_prop : KD.

(* Peirce律 *)
Fact law_peirce : forall Γ p q , Γ ├ ((p → q) → p) → p.
Proof.
  intros. apply Deductive_Theorem. assert (Γ ├ ¬p → (p → q)) by autoK. 
  apply Union_l with (A := [(p → q) → p]) in H. Single_Union.
Qed.

Global Hint Resolve law_peirce : KD.

(* (* 析取 *)
Notation " p ∨ q " := (¬p → q)(at level 7, right associativity).
Notation " p ∧ q " := (¬(p → ¬q))(at level 6, right associativity).
Notation " p ↔ q " := ((p → q)∧(q → p))
  (at level 9, right associativity).

Definition Disjunction p q := ¬p → q.
Notation " p ∨ q " := (Disjunction p q) (at level 7, right associativity).

Definition Conjunction p q := ¬(p → ¬q).
Notation " p ∧ q " := (Conjunction p q) (at level 6, right associativity).

Definition Equivalent p q := (p → q) ∧ (q → p).
Notation " p ↔ q " := (Equivalent p q)(at level 9, right associativity).
 *)
Proposition prop_3_5_1 : forall p q Γ, Γ ├ p → (p ∨ q).
Proof.
  intros. pose proof (law_deny_antecedent Γ q ¬p).
  pose proof (law_double_negation_second Γ p).
  pose proof (Syllogism Γ p ¬¬p (¬p → q)). pose proof (MP _ _ _ H1 H0).
  pose proof (MP _ _ _ H2 H). apply H3.
Qed.

Proposition prop_3_5_2 : forall p q Γ, Γ ├ q → (p ∨ q).
Proof. intros. apply K1. apply P1. Qed.

Proposition prop_3_5_3 : forall p q Γ, Γ ├ (p ∨ q) → (q ∨ p).
Proof.
  intros. apply Deductive_Theorem. apply -> Deductive_Theorem.
  assert (Γ ∪ [¬p → q] ∪ [¬q] ∪ [¬p] ├ q). { apply MP with (¬p); autoK. }
  assert (Γ ∪ [¬p → q] ∪ [¬q] ∪ [¬p] ├ ¬q) by autoK.
  apply (rule_Indirect (Γ ∪ [¬p → q] ∪ [¬q]) p q H H0).
Qed.

Proposition prop_3_5_4 : forall p Γ, Γ ├ (p ∨ p) → p.
Proof.
  intros. apply Deductive_Theorem.
  assert ([p ∨ p] ├ p). { assert ([p ∨ p] ├ p ∨ p) by autoK.
    apply Deductive_Theorem in H. assert ([p ∨ p] ├ ¬p → ¬p) by autoK.
    apply Deductive_Theorem in H0. apply rule_Indirect with p; auto. }
  apply Union_r_A. auto.
Qed.

Proposition prop_3_5_5 : forall p q r Γ, Γ ├ (q → r) → ((p ∨ q) → (p ∨ r)).
Proof.
  intros. apply Deductive_Theorem. repeat apply -> Deductive_Theorem.
  assert (Γ ∪ [q → r] ∪ [p ∨ q] ∪ [¬p] ├ ¬p) by autoK.
  assert (Γ ∪ [q → r] ∪ [p ∨ q] ∪ [¬p] ├ ¬p → q) by autoK.
  pose proof (MP _ _ _ H0 H).
  assert (Γ ∪ [q → r] ∪ [p ∨ q] ∪ [¬p] ├ q → r) by autoK.
  pose proof (MP _ _ _ H2 H1). auto.
Qed.

Proposition prop_3_5_6 : forall p Γ, Γ ├ ¬p ∨ p.
Proof. intros. pose proof (law_double_negation Γ p). apply H. Qed.

Proposition prop_3_6_1 : forall p q Γ, Γ ├ (p ∧ q) → p.
Proof.
  intros. pose proof (law_deny_antecedent Γ ¬q p).
  pose proof (law_inverse_prop Γ (p → ¬q) ¬p). pose proof (MP _ _ _ H0 H).
  pose proof (law_double_negation Γ p). pose proof (Syllogism Γ ¬(p → ¬q) ¬¬p p).
  pose proof (MP _ _ _ H3 H1). pose proof (MP _ _ _ H4 H2). auto.
Qed.

Proposition prop_3_6_2 : forall p q Γ, Γ ├ (p ∧ q) → q.
Proof.
  intros. assert (Γ ├ ¬q → p → ¬q) by autoK.
  pose proof (law_inverse_prop Γ (p → ¬q) ¬q). pose proof (MP _ _ _ H0 H).
  pose proof (law_double_negation Γ q). pose proof (Syllogism Γ ¬(p → ¬q) ¬¬q q).
  pose proof (MP _ _ _ H3 H1). pose proof (MP _ _ _ H4 H2). auto.
Qed.

Proposition prop_3_6_3 : forall p q Γ, Γ ├ (p ∧ q) → (q ∧ p).
Proof.
  intros. apply MP with ((q → ¬p) → (p → ¬q)).
  apply law_inverse_prop. repeat apply -> Deductive_Theorem.
  assert (Γ ∪ [q → ¬p] ∪ [p] ∪ [q] ├ p) by autoK.
  assert (Γ ∪ [q → ¬p] ∪ [p] ∪ [q] ├ ¬p). { apply MP with q; autoK. }
  apply (rule_Reduction_absurdity (Γ ∪ [q → ¬p] ∪ [p]) q p H H0).
Qed.

Proposition prop_3_6_4 : forall p Γ, Γ ├ p → (p ∧ p).
Proof.
  intros. apply Deductive_Theorem. assert (Γ ∪ [p] ∪ [p → ¬p] ├ p) by autoK.
  assert (Γ ∪ [p] ∪ [p → ¬p] ├ ¬p). { apply MP with p; autoK. }
  apply (rule_Reduction_absurdity (Γ ∪ [p]) (p → ¬p) p H H0).
Qed.

Proposition prop_3_6_5 : forall p q Γ, Γ ├ p → (q → (p ∧ q)).
Proof.
  intros. repeat apply -> Deductive_Theorem.
  assert (Γ ∪ [/p] ∪ [/q] ∪ [/p → ¬q] ├ q) by autoK.
  assert (Γ ∪ [/p] ∪ [/q] ∪ [/p → ¬q] ├ ¬q). { apply MP with p; autoK. }
  apply (rule_Reduction_absurdity (Γ ∪ [/p] ∪ [/q]) (p → ¬q) q H H0).
Qed.

Proposition prop_3_6_6 : forall p Γ, Γ ├ ¬(p ∧ ¬p).
Proof. intros. apply MP with (p → ¬¬p); apply law_double_negation_second. Qed. 

Proposition prop_3_7_1 : forall p q Γ, Γ ├ (p ↔ q) → (p → q).
Proof. intros. apply prop_3_6_1. Qed.

Proposition prop_3_7_2 : forall p q Γ, Γ ├ (p ↔ q) → (q → p).
Proof. intros. apply prop_3_6_2. Qed.

Lemma equivalent_theorem : forall p q Γ, Γ ├ (p ↔ q) <-> Γ ├ p → q /\ Γ ├ q → p.
Proof.
  intros. split.
  - intro. split.
    + apply MP with (p ↔ q). apply prop_3_7_1. auto.
    + apply MP with (p ↔ q). apply prop_3_7_2. auto.
  - intro. destruct H. specialize (prop_3_6_5 (p → q) (q → p)). 
    intros. pose proof MP _ _ _ (H1 Γ) H. apply MP with (q → p); auto.
Qed.

Proposition prop_3_7_3 : forall p q Γ, Γ ├ (p ↔ q) ↔ (q ↔ p).
Proof. intros. apply equivalent_theorem. split; apply prop_3_6_3. Qed.

Fact E511: forall Γ p q, Γ ├ (p → ¬q) → (q → ¬p).
Proof.
  intros. apply Deductive_Theorem. apply -> Deductive_Theorem.
  pose proof rule_Reduction_absurdity (Γ ∪ [p → ¬ q] ∪ [q]) p.
  apply H with q; autoK. apply MP with p; autoK.
Qed.

Proposition prop_3_7_4 : forall p q Γ, Γ ├ (p ↔ q) ↔ (¬p ↔ ¬q).
Proof.
  intros. apply equivalent_theorem. split; apply Deductive_Theorem; 
  apply equivalent_theorem; split; apply -> Deductive_Theorem.
  - assert (Γ ∪ [(p → q) ∧ (q → p)] ∪ [¬p] ├ (p → q) ∧ (q → p)) by autoK.
    assert (Γ ∪ [(p → q) ∧ (q → p)] ∪ [¬p] ├ q → p).
      { apply MP with ((p → q) ∧ (q → p)). apply prop_3_6_2. auto. }
    pose proof (law_inverse_prop (Γ ∪ [p → q ∧ q → p] ∪ [¬p]) q p). autoK.
  - assert (Γ ∪ [(p → q) ∧ (q → p)] ∪ [¬q] ├ (p → q) ∧ (q → p)) by autoK.
    assert (Γ ∪ [(p → q) ∧ (q → p)] ∪ [¬q] ├ p → q).
      { apply MP with (p → q ∧ q → p); autoK. }
    pose proof (law_inverse_prop (Γ ∪ [(p → q) ∧ (q → p)] ∪ [¬q]) p q). autoK.
  - assert (Γ ∪ [(¬p → ¬q) ∧ (¬q → ¬p)] ∪ [p] ├ ((¬p → ¬q) ∧ (¬q → ¬p))) 
      by autoK. assert (Γ ∪ [(¬p → ¬q) ∧ (¬q → ¬p)] ∪ [p] ├ ¬q → ¬p).
        { apply MP with ((¬p → ¬q) ∧ (¬q → ¬p)). apply prop_3_6_2. auto. }
    pose proof (E511 (Γ ∪ [(¬p → ¬q) ∧ (¬q → ¬p)] ∪ [p]) (¬q) (p)).
    pose proof (MP _ _ _ H1 H0).
    assert (Γ ∪ [(¬p → ¬q) ∧ (¬q → ¬p)] ∪ [p] ├ p) by autoK.
    pose proof (MP _ _ _ H2 H3).
    pose proof (law_double_negation (Γ ∪ [(¬p → ¬q) ∧ (¬q → ¬p)] ∪ [p]) q).
    pose proof (MP _ _ _ H5 H4). auto.
  - assert (Γ ∪ [(¬p → ¬q) ∧ (¬q → ¬p)] ∪ [q] ├ ((¬p → ¬q) ∧ (¬q → ¬p))) 
      by autoK. assert (Γ ∪ [(¬p → ¬q) ∧ (¬q → ¬p)] ∪ [q] ├ ¬p → ¬q).
        { apply MP with ((¬p → ¬q) ∧ (¬q → ¬p)). apply prop_3_6_1. auto. }
    pose proof (E511 (Γ ∪ [(¬p → ¬q) ∧ (¬q → ¬p)] ∪ [q]) (¬p) (q)).
    pose proof (MP _ _ _ H1 H0).
    assert (Γ ∪ [(¬p → ¬q) ∧ (¬q → ¬p)] ∪ [q] ├ q) by autoK.
    pose proof (MP _ _ _ H2 H3).
    pose proof (law_double_negation (Γ ∪ [(¬p → ¬q) ∧ (¬q → ¬p)] ∪ [q]) p).
    pose proof (MP _ _ _ H5 H4). auto.
Qed.

Proposition prop_3_7_5 : forall p q Γ, Γ ├ (p → q) → ((q → p) → (p ↔ q)).
Proof.
  intros. repeat apply -> Deductive_Theorem.
  apply equivalent_theorem. split; autoK.
Qed.

Proposition DeMorgan: forall p q Γ, Γ ├ ¬(p ∧ q) ↔ (¬p ∨ ¬q).
Proof.
  intros. apply equivalent_theorem. split; repeat apply -> Deductive_Theorem.
  - assert(Γ ∪ [¬¬(p → ¬q)] ∪ [¬¬p] ├ p → ¬q) by autoK. autoK.
  - apply MP with (p → ¬q). autoK. apply -> Deductive_Theorem.
    assert(Γ ∪ [¬¬p → ¬q] ∪ [p] ├ ¬¬p → ¬q) by autoK.
    assert (Γ ∪ [¬p ∨ ¬q] ∪ [p → ¬q] ├ p → ¬q) by autoK.
    pose proof (law_double_negation_second (Γ ∪ [¬p ∨ ¬q] ∪ [p → ¬q]) (p → ¬q)).
    pose proof (MP _ _ _ H1 H0). auto. apply -> Deductive_Theorem.
    assert (Γ ∪ [¬¬p → ¬q] ∪ [p] ├ ¬¬p → ¬q) by autoK.
    assert (Γ ∪ [¬¬p → ¬q] ∪ [p] ├ ¬¬p). autoK. pose proof (MP _ _ _ H H0). auto.
Qed.


Proposition DeMorgan': forall p q Γ, Γ ├ ¬(p ∨ q) ↔ (¬p ∧ ¬q).
Proof.
  intros. apply equivalent_theorem. split; repeat apply -> Deductive_Theorem.
  - assert (Γ ∪ [¬(¬p → q)] ∪ [¬p → ¬¬q] ├ ¬ (¬p → q)) by autoK.
    assert (Γ ∪ [¬(¬p → q)] ∪ [¬p → ¬¬q] ├ ¬p) by autoK.
    assert (Γ ∪ [¬(¬p → q)] ∪ [¬p → ¬¬q] ├ ¬q) by autoK.
    assert (Γ ∪ [¬(¬p → q)] ∪ [¬p → ¬¬q] ├ ¬¬q) by autoK.
    apply rule_Reduction_absurdity with (¬q); auto.
  - assert (Γ ∪ [¬(¬p → ¬¬q)] ∪ [¬p → q] ├ ¬ (¬p → ¬¬q)) by autoK.
    assert (Γ ∪ [¬(¬p → ¬¬q)] ∪ [¬p → q] ├ ¬p ) by autoK.
    assert (Γ ∪ [¬(¬p → ¬¬q)] ∪ [¬p → q] ├ q ) by autoK.
    assert (Γ ∪ [¬(¬p → ¬¬q)] ∪ [¬p → q] ├ ¬q ) by autoK.
    apply rule_Reduction_absurdity with q; auto.
Qed.


(* ================================================================ *)
(* 与量词相关的一些命题 *)

(* 量词推广规则 *)
Fact Gen_Rule : forall x p, ├ p -> ├ (∀ x, p).
Proof.
  intros. induction H. destruct H.
  - apply K1. apply C2. auto.
  - apply MP with (∀ x, p).
    apply MP with (∀ x, (p → q)). apply K1. apply D'.
    auto. auto.
Qed.


Fact Gen_Rule_1 : forall Γ x p, 
  ~(x ∈ (Formula_free_Ens p)) -> Γ ├ p -> Γ ├ (∀ x, p).
Proof.
  intros. assert (Γ ├ p → (∀ x, p)). { apply K1. apply C1. auto. }
  pose proof (MP _ _ _ H1 H0). auto.
Qed.

Fact Gen_Rule_1' : forall x p Γ,
  (forall q, q ∈ Γ -> ~ (x ∈ (Formula_free_Ens q)))
  -> Γ ├ p -> Γ ├ (∀ x, p).
Proof.
  intros. induction H0.
  - assert (~ (x ∈ (Formula_free_Ens p))) by (apply H; auto).
    apply MP with p. apply K1. apply C1. auto. apply K0. auto.
  - apply K1. apply C2. auto.
  - assert (Axiom_system ((∀ x, (p → q)) → (∀ x, p) → (∀ x, q))) by apply D'.
    apply MP with (∀ x, p); auto. apply MP with (∀ x, (p → q)); auto.
    apply K1. apply H0.
Qed.


(* 在项t中把变元x替换成自身Tvar x, 项不变 *)
Fact subst_t_id : forall t x, substitute_t t (Tvar x) x = t.
Proof.
  fix IH 1. intros. destruct t.
  - simpl. destruct (eqbv x v) eqn:E. unfold eqbv in E. destruct x.
    destruct v; auto. apply Nat.eqb_eq in E. subst; auto. auto.
  - simpl. auto.
  - simpl. f_equal. induction t eqn:H.
    + auto.
    + f_equal.
      * apply IH.
      * eapply IHt0; eauto.
Qed.

Check Nat.eqb_eq.
(* Nat.eqb_eq : forall n m : nat, (n =? m) = true <-> n = m *)

(* 项向量替换 *)
Fact subst_v_id : forall n v x, substitute_v n v (Tvar x) x = v.
Proof.
  induction v; simpl; auto. intros. rewrite IHv. rewrite subst_t_id. auto.
Qed.

(* 公式替换 *)
Fact subst_f_id : forall p x, substitute_f p (Tvar x) x = p.
Proof.
  induction p; simpl; intros; auto.
  - rewrite subst_t_id, subst_t_id. auto.
  - rewrite subst_v_id. auto.
  - rewrite IHp. auto.
  - rewrite IHp1, IHp2. auto.
  - destruct (eqbv x v); auto. rewrite IHp. auto.
Qed.

Fact subst' : forall p x y, ~ (y ∈ (Formula_Ens p))
  -> t_x_free p (Tvar y) x = true.
Proof.
  induction p; simpl; intros; auto. apply union_complement_equiv in H as [].
  rewrite IHp1,IHp2; auto. apply union_complement_equiv in H as [].
  destruct (classicT (x ∈ (Formula_free_Ens p) ~ [/v])); auto.
  destruct (classicT (v ∈ [/y])). elim H0. apply Single in i0. subst.
  apply In_singleton. apply IHp. auto.
Qed.

Fact eqbv_eq: forall x v, eqbv x v = true -> x = v.
Proof.
  intros. unfold eqbv in H. destruct x,v. rewrite Nat.eqb_eq in H.
  subst; auto.
Qed.

Fact eqbv_neq: forall x v, eqbv x v = false -> x <> v.
Proof.
  intros. unfold eqbv in H. destruct x,v. intro.
  inversion H0. rewrite H2 in H. rewrite Nat.eqb_refl in H. inversion H.
Qed.

Ltac Eqbv :=
  match goal with
  | H: eqbv ?x ?x = false |- _
    => destruct x; unfold eqbv in H; rewrite Nat.eqb_refl in H; inversion H
  | |- eqbv ?x ?x = true
    => destruct x; unfold eqbv; rewrite Nat.eqb_refl; auto
  | H: eqbv ?x ?v = true |- _ => apply eqbv_eq in H; subst
  | |- eqbv ?x ?v = true => apply eqbv_eq
  | H: eqbv ?x ?v = false |- _ => apply eqbv_neq in H
  | |- eqbv ?x ?v = false => apply eqbv_neq
  end.

Fact subst_term_removes : forall t x y, x <> y
  -> ~ x ∈ (term_Ens (t {x;(Tvar y)})).
Proof.
  fix IH 1. intros. destruct t.
  - simpl. destruct (eqbv x v) eqn:E; simpl; Eqbv; intro; ES.
    apply Single in H0. contradiction. apply Single in H0. contradiction.
  - simpl. intro. destruct H0.
  - simpl. intro. induction t; simpl; intros. destruct H0.
    apply UnionI in H0 as []. apply IH in H0; auto. apply IHt. auto.
Qed.

Fact vector_subst_removes : forall n v x y, x <> y ->
  ~ x ∈ (Vector_Ens n (substitute_v n v (Tvar y) x)).
Proof.
  induction v; simpl; intros. intro. destruct H0.
  apply union_complement_equiv. split. apply subst_term_removes. auto.
  apply IHv. auto.
Qed.

Fact subst_term_inv : forall t x y, ~ (y ∈ (term_Ens t))
  -> ((t {x;(Tvar y)}) {y;(Tvar x)}) = t.
Proof.
  fix IH 1. intros. destruct t.
  - simpl. destruct (eqbv x v) eqn:E. simpl. Eqbv.
    destruct (eqbv y y) eqn:E; auto. Eqbv. simpl.
    destruct (eqbv y v) eqn:E'; auto. simpl in H. Eqbv. elim H. ES.
  - simpl. auto.
  - simpl. f_equal. simpl in H. revert H. induction t; simpl; intros. auto.
    f_equal. apply IH. intro. apply H. left. auto.
    apply IHt. intro. apply H. right. auto.
Qed.

Fact subst_vector_inv : forall n v x y, ~ (y ∈ (Vector_Ens n v))
  -> substitute_v n (substitute_v n v (Tvar y) x) (Tvar x) y = v.
Proof.
  induction v; simpl; intros. auto.
  apply union_complement_equiv in H as []. f_equal.
  apply subst_term_inv. auto. apply IHv. auto.
Qed.

Fact subst_term_ignore : forall t x s, ~ (x ∈ (term_Ens t))
  -> t{x;s} = t.
Proof.
  fix IH 1. intros. destruct t.
  - simpl in H. simpl. destruct (eqbv x v) eqn:E; auto. Eqbv. elim H. ES.
  - simpl. auto.
  - simpl. f_equal. simpl in H. revert H. induction t; simpl; intros. auto.
    f_equal. apply IH. intro. apply H. left. auto.
    apply IHt. intro. apply H. right. auto.
Qed.

Fact subst_v_ignore : forall n v x s, ~ (x ∈ (Vector_Ens n v))
  -> substitute_v n v s x = v.
Proof.
  induction v; simpl; intros; auto.
  apply union_complement_equiv in H as []. rewrite subst_term_ignore; auto.
  rewrite IHv; auto.
Qed.

Fact subst_f_ignore : forall p x t, ~ (x ∈ (Formula_free_Ens p))
  -> p{x;;t} = p.
Proof.
  induction p; simpl; intros; auto.
  - apply union_complement_equiv in H as []. rewrite !subst_term_ignore; auto.
  - rewrite subst_v_ignore; auto.
  - rewrite IHp; auto.
  - apply union_complement_equiv in H as []. rewrite IHp1, IHp2; auto.
  - destruct (eqbv x v) eqn:E; auto. f_equal. apply IHp. red. intro.
    elim H. split; auto. intro. apply Single in H1. Eqbv. contradiction.
Qed.

Fact sub_xy_1: forall p x y, ~ (y ∈ (Formula_Ens p))
  -> x <> y -> ~ x ∈ (Formula_free_Ens (p) {x;;Tvar y}).
Proof.
  intros. induction p; auto.
  - simpl in H. apply union_complement_equiv in H as [].
    red. intro. simpl in H2. apply UnionI in H2 as [];
    apply subst_term_removes in H2; auto.
  - simpl. simpl in H. red. intro.
    eapply (vector_subst_removes (arity_R r)) in H0; eauto.
  - apply union_complement_equiv in H as []. apply union_complement_equiv.
    split. apply IHp1; auto. apply IHp2; auto.
  - red. intro. simpl in H1. destruct (eqbv x v) eqn:E. destruct H1.
    elim H2. Eqbv. ES. Eqbv. apply union_complement_equiv in H as [].
    apply IHp in H. simpl in H1. destruct H1. contradiction.
Qed.

Fact sub_xy_2: forall p x y, ~ (y ∈ (Formula_Ens p))
  -> (p {x ;; Tvar y}) {y ;; Tvar x} = p.
Proof.
  intros. induction p; simpl; intros; auto.
  - simpl in H. apply union_complement_equiv in H as [].
    eapply (subst_term_inv _ x) in H,H0; eauto. rewrite H,H0. auto.
  - simpl in H. f_equal. eapply subst_vector_inv in H; eauto.
  - rewrite IHp; auto.
  - apply union_complement_equiv in H as []. rewrite IHp1, IHp2; auto.
  - simpl in H. apply union_complement_equiv in H as [].
    destruct (eqbv x v) eqn:E; simpl; destruct (eqbv y v) eqn:E'; auto.
    * f_equal. eapply subst_f_ignore; eauto. intro.
      apply free_contain_Ens in H1. auto.
    * Eqbv. elim H0. ES.
    * f_equal. apply IHp; auto.
Qed.

Fact sub_xy_3: forall p x y, ~ (y ∈ (Formula_Ens p))
  -> x <> y -> t_x_free (p) {x;; Tvar y} (Tvar x) y = true.
Proof.
  induction p; simpl; auto; intros.
  - apply union_complement_equiv in H as []. rewrite IHp1, IHp2; auto.
  - apply union_complement_equiv in H as []. destruct (eqbv x v) eqn:E.
    simpl. destruct (classicT (y ∈ (Formula_free_Ens p) ~ [/v])); auto.
    destruct i. apply free_contain_Ens in H2. contradiction. simpl.
    apply (IHp x) in H; auto. rewrite H.
    destruct (classicT (y ∈ (Formula_free_Ens (p) {x;; Tvar y}) ~ [/v])); auto.
    destruct (classicT (v ∈ [/x])); auto. apply Single in i0. Eqbv.
    symmetry in i0. contradiction.
Qed.

Example exam_3_1: forall p x, [¬∃ x, ¬p] ├ (∀ x, p).
Proof.
  intros. 
  assert (H1: [¬∃ x, ¬p] ├ ¬∃ x, ¬p) by (apply K0; apply In_singleton).
  unfold Exists at 2 in H1.
  assert (H2: [¬∃ x, ¬p] ├ (¬¬(∀ x, (¬¬p))) → (∀ x, (¬¬p))).
    { apply law_double_negation. }
  assert (H3: [¬∃ x, ¬p] ├ ∀ x, (¬¬p)). { eapply MP; eauto. }
  assert (H4: [¬∃ x, ¬p] ├ (∀ x, (¬¬p)) → (¬¬p)).
    { pose proof (S' (¬¬p) x (Tvar x)). rewrite subst_f_id in H.
      apply K1. apply H. apply free_test_3. }
  assert (H5: [¬∃ x, ¬p] ├ ¬¬p). { eapply MP; eauto. }
  assert (H6: [¬∃ x, ¬p] ├ ¬¬p → p). { apply law_double_negation. }
  assert (H7: [¬∃ x, ¬p] ├ p). { apply MP with (¬¬p); auto. }
  assert (H8: [¬(∃ x, ¬p)] ├ ∀ x, p).  
    { assert (H1': ├ ¬(∃ x, ¬p) → p).
        { assert(Φ ∪ [¬(∃ x, ¬p)] ├ p). eapply Union_r_A; eauto.
          apply (Deductive_Theorem (@ Φ) (¬(∃ x, ¬p)) p). auto. }
      assert (H2': ├ ∀ x, (¬(∃ x, ¬p) → p)). { eapply Gen_Rule. eauto. }
      assert (H3': ├ (∀ x, ((¬∃ x, ¬p) → p)) → (∀ x, ¬(∃ x, ¬p)) → (∀ x, p)).
        { apply K1. apply D'. }
      pose proof (MP _ _ _ H3' H2') as H4'.
      assert (H5': [¬∃ x, ¬p] ├ ∀ x, (¬∃ x, ¬p)). 
        { apply MP with (¬∃ x, ¬ p).
          - apply K1. apply C1. unfold Exists. red. intro H.
            destruct H as [_ H]. elim H. apply In_singleton.
          - apply K0. apply In_singleton. }
      apply MP with (∀ x, ¬(∃ x, ¬p)); auto.
      apply subsetprove with (A := Φ).
      unfold Included. intros. destruct H. auto. }
  auto.
Qed.

(* 永真式 (q → ¬p) → (p → ¬q) *)
Fact law_inverse_prop_1: forall Γ p q, Γ ├ (q → ¬p) → (p → ¬q).
Proof.
  intros. apply Deductive_Theorem. apply -> Deductive_Theorem.
  assert (Γ ∪ [q → ¬p] ∪ [p] ∪ [q] ├ p) by autoK.
  assert (Γ ∪ [q → ¬p] ∪ [p] ∪ [q] ├ ¬p).
    { assert (Γ ∪ [q → ¬p] ∪ [q] ├ q) by autoK.
      assert (Γ ∪ [q → ¬p] ∪ [q] ├ q → ¬p) by autoK.
      pose proof (MP _ _ _ H1 H0) as H2.
      apply subsetprove with (A := Γ ∪ [q → ¬p] ∪ [q]).
      red. intros. destruct H3; ES. auto. }
  pose proof (rule_Reduction_absurdity (Γ ∪ [q → ¬p] ∪ [p]) q p) as H1.
  apply H1 in H. auto. auto.
Qed.

Proposition prop_3_9: forall x p t, t_x_free p t x = true -> ├ p → (∃ x, p).
Proof.
  intros. assert (├ (∀ x, (¬p)) → (¬p)).
    { pose proof (S' (¬p) x (Tvar x)). rewrite subst_f_id in H0.
      apply K1. apply H0. apply free_test_3. }
  assert (├ ((∀ x, (¬p)) → (¬p)) → (p → ¬(∀ x, (¬p)))).
    { apply law_inverse_prop_1. }
  pose proof (MP _ _ _ H1 H0) as H2. auto.
Qed.

Fact Union_empty_l: forall A, Φ ∪ A = A.
Proof.
  intros. apply Extensionality_Ensembles. red. split.
  - red. intros. destruct H. destruct H. auto.
  - red. intros. right. auto.
Qed.

Example exam_3_2: forall p q x, [∀ x, (p → q)] ∪ [∀ x, ¬q] ├ (∀ x, (¬p)).
Proof.
  intros. assert (├ (p → q) → ¬q → ¬p).
    { apply Deductive_Theorem. apply -> Deductive_Theorem.
      assert (Φ ∪ [p → q] ∪ [¬q] ∪ [p] ├ ¬q) by autoK.
      assert (Φ ∪ [p → q] ∪ [¬q] ∪ [p] ├ q).
        { assert (Φ ∪ [p → q] ∪ [p] ├ p) by autoK.
          assert (Φ ∪ [p → q] ∪ [p] ├ p → q) by autoK.
          pose proof (MP _ _ _ H1 H0) as H2.
          apply subsetprove with (A := Φ ∪ [p → q] ∪ [p]).
          red. intros. destruct H3; ES. auto. }
      pose proof (rule_Reduction_absurdity (Φ ∪ [p → q] ∪ [¬q]) p q) as H1.
      apply H1 in H0. auto. auto. }
  assert (H1: ├ ∀ x, ((p → q) → ¬q → ¬p)). { eapply Gen_Rule. eauto. }
  assert (H2: ├ (∀ x, ((p → q) → ¬q → ¬p))
    → (∀ x, ((p → q)) →  (∀ x,(¬q → ¬p)))). { apply K1. apply D'. }
  pose proof (MP _ _ _ H2 H1). apply Deductive_Theorem in H0.
  assert (Φ ∪ [∀ x, (p → q)] ├ (∀ x, (¬q → ¬p))
    → (∀ x, ¬q) → (∀ x, ¬p)). { apply K1. apply D'. }
  pose proof (MP _ _ _ H3 H0). apply Deductive_Theorem in H4.
  rewrite Union_empty_l in H4. auto.
Qed.

Proposition prop_3_10: forall p q x, ├ (∀ x, (p → q)) → ((∃ x, p) → (∃ x, q)).
Proof.
  intros. pose proof (exam_3_2 p q x). apply Deductive_Theorem in H.
  pose proof (law_inverse_prop [∀ x, (p → q)] (∀ x, ¬p) (∀ x, ¬q)).
  pose proof (MP _ _ _ H0 H). apply Deductive_Theorem.
  rewrite Union_empty_l. auto.
Qed.

Example exam_3_3: forall p x, [∀ x, p] ├ (∃ x, p).
Proof.
  intros. assert ([∀ x, p] ∪ [∀ x, ¬p]├ ∀ x, ¬p) by autoK.
  assert ([∀ x, p] ∪ [∀ x, ¬p]├ ∀ x, p) by autoK.
  assert ([∀ x, p] ∪ [∀ x, ¬p]├ (∀ x, ¬p) → ¬p).
    { pose proof (S' (¬p) x (Tvar x)). rewrite subst_f_id in H1.
      apply K1. apply H1. apply free_test_3. }
  assert ([∀ x, p] ∪ [∀ x, ¬p]├ (∀ x, p) → p).
    { pose proof (S' p x (Tvar x)). rewrite subst_f_id in H2.
      apply K1. apply H2. apply free_test_3. }
  pose proof (MP _ _ _ H1 H). pose proof (MP _ _ _ H2 H0).
  pose proof (rule_Reduction_absurdity [∀ x, p] (∀ x, ¬p) p). 
  apply H5 in H4. apply H4. apply H3.
Qed.


Proposition prop_3_11: forall Γ p q x, Γ ∪ [p] ├ q 
  -> ~(x ∈ (Formula_free_Ens p)) -> ~(x ∈ (Formula_free_Ens q))
  ->  Γ ∪ [∃ x, p] ├ q.
Proof.
  intros. apply Deductive_Theorem in H. pose proof (law_inverse_prop Γ q p).
  pose proof (MP _ _ _ H2 H). assert (Γ ├ ∀ x, (¬q → ¬p)).
    { apply Gen_Rule_1. auto. red. intro.
      simpl in H4. Search ( ?x ∈ (?A ∪ ?B)). apply UnionI in H4.
      destruct H4. destruct H1. auto. destruct H0; auto. auto. }
  assert (Γ ├ (∀ x, (¬q → ¬p)) → (∀ x, ¬q) → (∀ x, ¬p)). { apply K1, D'. }
  pose proof (MP _ _ _ H5 H4).
  assert (Γ ├ ((∀ x, ¬q) → (∀ x, ¬p)) → (¬(∀ x, ¬p) → ¬(∀ x, ¬q))).
    { pose proof (law_inverse_prop Γ (∀ x, ¬p) (∀ x, ¬q)). auto. }
  pose proof (MP _ _ _ H7 H6). apply Deductive_Theorem in H8.
  assert (H9: Γ ∪ [¬(∀ x, ¬p)] ├ ¬(∀ x, ¬q) → ¬¬q).
    { assert (Γ ├ ¬q → (∀ x, ¬q)). { apply K1. apply C1. simpl. auto. }
      assert (Γ ├ (¬q → (∀ x, ¬q)) → (¬(∀ x, ¬q) → ¬¬q)).
        { pose proof (law_inverse_prop Γ (∀ x, ¬q) ¬q). auto. }
      pose proof (MP _ _ _ H10 H9). apply subsetprove with (A := Γ).
      unfold Included. intros. left. auto. auto. }
  pose proof (MP _ _ _ H9 H8). assert (Γ ∪ [¬(∀ x, ¬p)] ├ ¬¬q → q).
    { pose proof (law_double_negation (Γ ∪ [¬(∀ x, ¬p)]) q). auto. }
  pose proof (MP _ _ _ H11 H10). auto.
Qed.

Proposition prop_3_12_1: forall p x y, ~ (y ∈ (Formula_Ens p))
  -> ├ (∀ x, p) ↔ (∀ y, p{x;;(Tvar y)}).
Proof.
  intros. apply equivalent_theorem. split.
  - apply Deductive_Theorem. assert (Φ ∪ [∀ x, p] ├ ∀ x, p) by autoK.
    assert (Φ ∪ [∀ x, p] ├ (∀ x, p) → p{x;;(Tvar y)}).
      { apply K1. apply (S' p x (Tvar y)). apply subst'. auto. }
    pose proof (MP _ _ _ H1 H0). apply Gen_Rule_1'. intros.
    rewrite Union_empty_l in H3. apply Single in H3. subst. red. intro.
    destruct H3. apply free_contain_Ens in H3. elim H. auto. auto.
  - apply Deductive_Theorem. rewrite Union_empty_l. apply Gen_Rule_1'.
    + intros. apply Single in H0. subst. red. intro. destruct H0.
      apply sub_xy_1 in H0; auto. red. intro. elim H1. subst. apply In_singleton.
    + rewrite <- (sub_xy_2 p x y) at 2; auto.
      apply MP with (∀ y, (p {x ;; Tvar y})); autoK. apply K1. apply S'.
      destruct (classicT (x = y)). subst. apply free_test_3. 
      eapply sub_xy_3; eauto.
Qed.

Proposition prop_3_12_2: forall p x y, ~ (y ∈ (Formula_Ens p))
  -> ├ (∃ x, p) ↔ (∃ y, p{x;;(Tvar y)}).
Proof.
  intros. unfold Exists.
  pose proof (prop_3_7_4 (∀ x, ¬ p) (∀ y, ¬ (p) {x;; Tvar y}) Φ).
  apply equivalent_theorem in H0 as [H0 _]. apply (MP _ _ _ H0).
  apply prop_3_12_1. simpl. auto.
Qed.

(* Proposition prop_3_12_1': forall p x y, ~ (y ∈ (Formula_free_Ens p))
  -> ├ (∀ x, p) → (∀ y, p).
Proof.
  intros. apply Deductive_Theorem. assert (Φ ∪ [∀ x, p] ├ ∀ x, p) by autoK.
  assert (Φ ∪ [∀ x, p] ├ (∀ x, p) → p).
    { pose proof (S' p x (Tvar x)). rewrite subst_f_id in H1.
      apply K1. apply H1. apply free_test_3. }
  pose proof (MP _ _ _ H1 H0). apply Gen_Rule_1. auto. auto.
Qed.

Proposition prop_3_12_2': forall p x y, ~ (y ∈ (Formula_free_Ens p))
  -> ├ (∃ y, p) → (∃ x, p).
Proof.
  intros. assert (├ (∀ x, ¬p) → (∀ y, ¬p)).
    { apply Deductive_Theorem. assert (Φ ∪ [∀ x, ¬p] ├ ∀ x, ¬p) by autoK.
      assert (Φ ∪ [∀ x, ¬p] ├ (∀ x, ¬p) → ¬p).
        { pose proof (S' ¬p x (Tvar x)). rewrite subst_f_id in H1.
          apply K1. apply H1. apply free_test_3. }
      pose proof (MP _ _ _ H1 H0). apply Gen_Rule_1. auto. auto. }
  assert (├ ((∀ x, ¬p) → (∀ y, ¬p)) → (¬(∀ y, ¬p) → ¬(∀ x, ¬p))).
    { apply (law_inverse_prop Φ (∀ y, ¬p) (∀ x, ¬p)). }
  pose proof (MP _ _ _ H1 H0). auto.
Qed. *)

Proposition prop_3_13_1: forall p x, ├ (¬(∀ x, p)) ↔ (∃ x, ¬p).
Proof.
  intros. assert(├ (∀ x, ¬¬p) → (∀ x, p)).
    { assert(├ (∀ x, ¬¬p) → (¬¬p)).
        { pose proof (S' (¬¬p) x (Tvar x)). rewrite subst_f_id in H.
          apply K1. apply H. apply free_test_3. }
      assert(├ (¬¬p) → p).
        { apply Deductive_Theorem. eapply Union_r_A.
          apply law_double_negation_aux. }
      assert(├ (∀ x, ¬¬p) → p).
        { apply Deductive_Theorem in H0. apply Deductive_Theorem in H0.
          pose proof (syllogism Φ (∀ x, ¬¬p) (¬¬p) p).
          apply Deductive_Theorem in H, H0. apply H1 in H.
          apply Deductive_Theorem. auto. auto. }
      assert (├ ∀ x, (¬¬p → p)).
        { apply Gen_Rule. apply law_double_negation. }
      assert (├ (∀ x, (¬¬p → p)) → (∀ x, ¬¬p) → (∀ x, p)).
        { apply K1. apply D'. }
      pose proof (MP _ _ _ H3 H2). auto. }
  assert(├ (∀ x, p) → (∀ x, ¬¬p)).
    { assert(├ (∀ x, p) → p).
        { pose proof (S' p x (Tvar x)). rewrite subst_f_id in H0.
          apply K1. apply H0. apply free_test_3. }
      assert(├ p → (¬¬p)).
        { apply Deductive_Theorem. eapply Union_r_A.
          apply law_double_negation_second_aux. }
      assert(├ (∀ x, p) → (¬¬p)).
        { apply Deductive_Theorem in H0. apply Deductive_Theorem in H1.
          pose proof (syllogism Φ (∀ x, p) p (¬¬p)).
          apply H2 in H0; auto. apply Deductive_Theorem. auto. }
      assert (├ ∀ x, (p → ¬¬p)).
        { apply Gen_Rule. apply law_double_negation_second. }
      assert (├ (∀ x, (p → ¬¬p)) → (∀ x, p) → (∀ x, ¬¬p)).
        { apply K1. apply D'. }
      pose proof (MP _ _ _ H4 H3). auto. }
  apply equivalent_theorem. split.
  - pose proof (law_inverse_prop Φ (∀ x, p) (∀ x, ¬¬p)).
    pose proof (MP _ _ _ H1 H). auto.
  - pose proof (law_inverse_prop Φ (∀ x, ¬¬p) (∀ x, p)).
    pose proof (MP _ _ _ H1 H0). auto.
Qed.

Proposition prop_3_13_2: forall p x, ├ (¬(∃ x, p)) ↔ (∀ x, ¬p).
Proof.
  intros. assert(├ (¬¬(∀ x, ¬p)) ↔ (∀ x, ¬p)).
    { assert(├ (¬¬(∀ x, ¬p)) → (∀ x, ¬p)) by autoK.
      assert(├ (∀ x, ¬p) → (¬¬(∀ x, ¬p))) by autoK.
      apply equivalent_theorem. eauto. }
  unfold Exists. auto.
Qed.



