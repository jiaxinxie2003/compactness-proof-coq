(**************************************************************************)
(*  This is part of semantic_pc, it is distributed under the terms of the *)
(*            GNU Lesser General Public License version 3                 *)
(*               (see file LICENSE for more details)                      *)
(*                                                                        *)
(*                       Copyright 2023-2028                              *)
(*         Dakai Guo, qiming Wang, jianghao Liu and Wensheng Yu           *)
(**************************************************************************)

(** soundness_K_System *)

Require Import base_pc.
Require Import formulas_K_System.
Require Import syntax_K_System.
Require Import semantic_K_System.
Require Import Coq.Logic.Classical.

(* 有矛盾公式集 一致集 *)
(* Definition Contradiciton Γ := exists q, Γ ├ q /\ Γ ├ ¬q. *)

Definition consistence Γ := forall q, ~ (Γ ├ q /\ Γ ├ ¬q).

(* 一致集的性质 *)
Proposition redundancy_lemma : forall Γ p, Γ ∪ [/¬p] ├ p -> Γ ├ p.
Proof.
  intros. apply Deductive_Theorem in H. assert (Γ ├ (¬p → p) → p); autoK.
Qed.

(* 一致集的性质 *)
Proposition boom : forall Γ, ~ consistence Γ -> forall p, Γ ├ p.
Proof.
  intros. unfold consistence in H. apply not_all_not_ex in H as [? []].
  assert (Γ ├ x → ¬x → p); autoK. Unshelve. exact p. exact p. exact p. exact p.
Qed.

(* 一致集的性质 *)
Proposition No_contra : forall Γ, consistence Γ 
  -> forall p, consistence (Γ ∪ [/p]) \/ consistence (Γ ∪ [/¬p]).
Proof.
  intros. destruct (classic (consistence (Γ ∪ [/¬p]))); auto. pose proof boom.
  pose proof H1 (Γ ∪ [/¬p]) H0. pose proof H2 p. apply redundancy_lemma in H3.
  destruct (classic (consistence (Γ ∪ [/p]))); auto. pose proof H1 (Γ ∪ [/p]) H4.
  assert (forall p0, Γ ├ p0).
    { intros. pose proof H5 p0. apply Deductive_Theorem in H6.
      apply MP with p; auto. } 
  red in H. pose proof H p. destruct H7; split; auto.
Qed.

(* 极大一致集 *)
Definition maximal_consistent_set Γ := 
  consistence Γ /\ forall p, consistence (Γ ∪ [/p]) -> p ∈ Γ.

(* 3.5  *)
(* 可靠性定理引理 *)
Lemma Axiom_system_reliable : forall p , Axiom_system p -> ╞ p.
Proof.
  intros. induction H.
  - apply T_3_6_1.
  - apply T_3_6_2.  
  - apply T_3_6_3.
  - apply T_3_9. auto.
  - apply T_3_8.
  - apply T_3_7_1.
  - apply T_3_7_2.
  - apply T_3_7_3.
  - apply T_3_7_4.
  - apply T_3_7_5.
  - red. intros. simpl. destruct (classicT (satisfy_R MM v p)); auto. right. intros.
    assert(agreement_f v (value_v v x m) p).
      { red. intros. unfold value_v. destruct(classicT (x0 = x)).
        rewrite e in H0. apply H in H0. inversion H0. auto. }
    apply agree_fact_2 in H0; destruct H0. apply H0; auto.
  - apply exam_3_5. auto.
Qed.

(* (* 可靠性定理 *)
Definition sound := forall Γ p, Γ ├ p -> Γ ╞ p.

Theorem soundness : sound.
Proof.
 intros. red. intros. red. intros. induction H.
 - red in H0. apply H0 in H. auto.
 - apply Axiom_system_reliable. auto. 
 - apply exam_3_4 with p. red. intros.
   destruct H2; apply Single in H2; rewrite H2; auto.
Qed.  *) 

(* 可靠性定理 *)
Theorem soundness_K : forall p Γ ,Γ ├ p -> Γ ╞ p.
Proof.
  intros; red; intros. induction H.
  - red in H0. apply H0 in H. auto.
  - apply Axiom_system_reliable. auto. 
  - apply exam_3_4 with p. red. intros.
    destruct H2; apply Single in H2; rewrite H2; auto.
Qed.

Print Build_Module.

Definition modu :=     (Build_Module nat 
                       (fun _ => 0)
                       (fun _ _ => 0)
                       (fun _ _ => True)).
Definition vv := (fun (_:Var) => 0).

Theorem kong : satisfyable modu vv Φ.
Proof.
  red.
  intros.
  destruct H.
Qed.

Corollary consistence_K :  consistence Φ.
Proof.
  unfold consistence. intros. intro. destruct H. apply soundness_K in H, H0. 
  red in H; red in H0. simpl in H0.
  pose proof H modu vv kong.
  pose proof H0 modu vv kong.
  tauto.
Qed.

