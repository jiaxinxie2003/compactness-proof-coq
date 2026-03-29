(**************************************************************************)
(* This is part of compactness, it is distributed under the terms of the  *)
(*            GNU Lesser General Public License version 3                 *)
(*               (see file LICENSE for more details)                      *)
(*                                                                        *)
(*                       Copyright 2023-2028                              *)
(*         Dakai Guo, qiming Wang, jianghao Liu and Wensheng Yu           *)
(**************************************************************************)

(** compactness_K_System *)

Require Import base_pc.
Require Import formulas_K_System.
Require Import syntax_K_System.
Require Import semantic_K_System.
Require Import soundness_K_System. 
Require Import complete_K_System.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.

(* 紧致性：任给公式集 Γ 和公式 p , Γ ╞ p 当且仅当存在Γ的有穷子集 Γ' 使得 Γ' ╞ p *)
Theorem compactness : forall Γ p,
  Γ ╞ p <-> exists Γ', Γ' ⊆ Γ /\ Finite _ Γ' /\ Γ'╞ p.
Proof.
  split; intros.
  - apply complete_theorem in H. induction H.
    + exists [p]. repeat split. 
      * red. ES. apply Singleton_inv in H0. rewrite <- H0. auto.
      * apply Singleton_is_finite.
      * apply soundness_K. autoK. 
    + exists Φ. repeat split. 
      * red; ES.
      * Search Finite. apply Empty_is_finite.
      * apply soundness_K. autoK.
    + destruct IHdeduce_K1 as [Γ1 [? []]].
      destruct IHdeduce_K2 as [Γ2 [? []]].
      exists (Γ1 ∪ Γ2). repeat split.
      * ES.
      * apply Union_preserves_Finite; auto.
      * apply soundness_K. apply complete_theorem in H3, H6.
        pose proof Union_l _ _ H3 Γ2. pose proof Union_r _ _ H6 Γ1. autoK.
  - unfold Logically_implies in *. intros. destruct H as [Γ' [? []]].
    specialize (H2 MM v). apply H2. unfold Included in *. unfold satisfyable in *.
    intros. specialize (H0 p0). apply H in H3. apply H0 in H3. auto.
Qed.
(**************************************************************************)

(* 一致集都是可满足的 *)
(* Definition consistence_satisfiable := forall Γ, consistence Γ -> satisfyable_Γ Γ. *)
Lemma con_sat_theorem : consistence_satisfiable. 
Proof.
  red. intros. apply max_consistence_extension in H. 
  destruct H as [Γ' [? []]].
  assert ( satisfyable_Γ Γ' ). { apply satisfiable_theorem; auto. }
  unfold satisfyable_Γ in *. destruct H2 as [MM [v ?]]. 
  exists (Module2C MM), v. intros p Hp. 
  assert ( (double_C_set Γ) (double_C_formula p) ).
  { apply double_C_set_intro; auto. }
  assert ( Γ' (double_C_formula p) ). { apply H0. auto. }
  assert ( {MM; v} |= (double_C_formula p) ). { apply H2; auto. }
  apply (double_C_satisfy' MM v p). auto.
Qed.

(* 可满足的都是一致集 *)
Lemma sat_con_theorem : forall Γ, satisfyable_Γ Γ -> consistence Γ.
Proof.
  red. intros. intro. destruct H0. auto. apply soundness_K in H0, H1.
  Search (?Γ ╞ ?q). apply exam_3_6_2 in H1. apply exam_3_6_1 in H0.
  destruct H as [MM [v ?]]. unfold satisfyable_Γ, satisfyable in *.
  assert ({MM; v} |= q \/ {MM; v} |= ¬ q). { apply classic. }   
  destruct H2 as [Hq | Hnq].
  - apply H1. exists MM, v. intros p Hp. destruct Hp.
    + apply H; auto.
    + destruct H2. subst. assumption.
  - apply H0. exists MM, v. intros p Hp. destruct Hp.
    + apply H; auto.
    + destruct H2. subst. assumption.
Qed.

Lemma satisfyable_subset : forall Γ1 Γ2,
  Γ1 ⊆ Γ2 -> satisfyable_Γ Γ2 -> satisfyable_Γ Γ1.
Proof.
  intros. unfold satisfyable_Γ, satisfyable in *.
  destruct H0 as [MM [v ?]]. exists MM, v. intros. specialize (H0 p).
  unfold Included in H. apply H in H1. apply H0 in H1. auto.
Qed.

Lemma unsatisfyable : forall Γ p, Γ ╞ (p ∧ ¬p) <-> ~ satisfyable_Γ Γ.
Proof.
  intros. split.
  - intros H1 H2. destruct H2 as [MM [v ?]]. specialize (H1 MM v H).
    apply H1. left. intro. apply H1. right. intro.  contradiction.
  - intros. unfold Logically_implies. intros. exfalso.
    apply H. exists MM, v. auto.
Qed.

(* 有限可满足：Γ是有限可满足的当且仅当Γ的所有有限子集Γ0都是可满足的 *)
Definition finitely_satisfiable Γ := 
  forall Γ0, Γ0 ⊆ Γ /\ Finite _ Γ0 -> satisfyable_Γ Γ0.

Theorem compactness_equiv : 
  (forall Γ p, Γ ╞ p <-> exists Γ', Γ' ⊆ Γ /\ Finite _ Γ' /\ Γ'╞ p)
  <-> (forall Γ, finitely_satisfiable Γ <-> satisfyable_Γ Γ).
Proof.
  split; intros.
  - split; intros.
    + destruct (classic (satisfyable_Γ Γ)) as [ ]; auto.
      apply con_sat_theorem. red. intros. exfalso.
      apply <- (unsatisfyable Γ q) in H1.
      apply H in H1 as [Γ' [? []]]. apply unsatisfyable in H3.
      unfold finitely_satisfiable in H0. specialize (H0 Γ'). auto.
    + unfold satisfyable_Γ in H0.
      destruct H0 as [MM [v ]]. red. exists MM, v.
      unfold satisfyable in *. intros. apply H0,H1. auto.
  - split; intros.
    + apply satisfiable_contra_le in H0.
      assert (~ finitely_satisfiable (Γ ∪ [/¬ p])).
      { unfold not. intros. specialize (H (Γ ∪ [/¬ p])). 
        destruct H. apply H in H1; auto. }
      unfold finitely_satisfiable in H1.
      apply not_all_ex_not in H1. destruct H1 as [Δ H1].
      apply not_all_ex_not in H1. destruct H1 as [H2 ?].
      destruct H2. set (Γ' := fun x => Δ x /\ Γ x).
      exists Γ'. repeat split.
      * unfold Included, Γ'. intros x [HxΔ HxΓ]. exact HxΓ.
      * eapply Finite_downward_closed. exact H3.
        unfold Included, Γ'. intros x [Hx _]. exact Hx.
      * apply satisfiable_contra_le.
        unfold not. intros Hsat.
        apply H1. eapply satisfyable_subset.
        2: exact Hsat.
        unfold Included, Γ'. intros x Hx.
        specialize (H2 x Hx).
        destruct H2; [left; split | right]; auto.
    + unfold Logically_implies in *. intros. destruct H0 as [Γ' [? []]].
      specialize (H3 MM v). apply H3. unfold Included in *. 
      unfold satisfyable in *. intros. specialize (H0 p0).
      apply H0 in H4. apply H1 in H4. auto.
Qed.
