(**************************************************************************)
(*  This is part of semantic_pc, it is distributed under the terms of the *)
(*            GNU Lesser General Public License version 3                 *)
(*               (see file LICENSE for more details)                      *)
(*                                                                        *)
(*                       Copyright 2023-2028                              *)
(*         Dakai Guo, qiming Wang, jianghao Liu and Wensheng Yu           *)
(**************************************************************************)

(** comolete_K_System *)

Require Import base_pc.
Require Import formulas_K_System.
Require Import syntax_K_System.
Require Import semantic_K_System.
Require Import soundness_K_System.
(* Require Export Coq.Bool.Bool. *)
(* Require Export Coq.Arith.Arith. *)
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Epsilon.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Vectors.Vector.
Import VectorNotations.
Require Import Program.

(* 完备性定理 *)
Definition complete := forall Γ p, Γ ╞ p -> Γ ├ p.

(* 完备性定理的逆否命题 *)
Definition complete_contra := forall Γ p, ~ (Γ ├ p) -> ~ (Γ ╞ p).

(* 关于一致性的一些简单事实 *)
(* ~(Γ├p)当且仅当Γ∪[/¬p]是一致的 *)
Fact consistence_contra : forall Γ p, ~ (Γ ├ p) <-> consistence (Γ ∪ [/¬p]).
Proof.
  split; intros.
  - red; intros. intro.
    destruct H0. destruct H. pose proof rule_Indirect _ _ _ H0 H1. auto.
  - intro. red in H.
    destruct (H p). split.
    + apply subsetprove with Γ; auto. red; intros. left; auto.
    + constructor. right. split.
Qed.

(* (Γ╞p)当且仅当Γ∪[/¬p]不是可满足的 *)
Fact satisfiable_contra_le : forall Γ p, Γ ╞ p <-> ~ satisfyable_Γ (Γ ∪ [/¬p]).
Proof.
  intros. split; red; intros.
  - red in H0. destruct H0 as [MM [v H0]]. 
    assert(satisfyable MM v Γ). { red in H0. red. intros. apply H0. left. auto. } 
    apply H in H1. pose proof H0. red in H0. specialize H0 with ¬p. 
    assert(¬p ∈ (Γ ∪ [/¬p])). { right. eauto with sets. } 
    apply H0 in H3. simpl in H3. auto.
  - red in H. unfold satisfyable_Γ in H. unfold satisfyable in H0.
    destruct(classic (p ∈ Γ) ). apply H0 in H1. auto.
    destruct(classic (satisfy_R MM v p)). auto.
    assert((exists (MM: Module) (v: value MM), satisfyable MM v (Γ ∪ [/¬p]))). 
      { exists MM,v. red. intros. destruct H3. apply H0. auto. destruct H3. 
        simpl; auto. }
    apply H in H3. destruct H3.
Qed.

(* ~(Γ╞p)当且仅当Γ∪[/¬p]是可满足的*)
Fact satisfiable_contra : forall Γ p, 
  ~ (Γ ╞ p) <-> satisfyable_Γ (Γ ∪ [/¬p]).
Proof. intros; rewrite satisfiable_contra_le; tauto. Qed.

(* 目标: 一致集都是可满足的 *)
Definition consistence_satisfiable := forall Γ, consistence Γ -> satisfyable_Γ Γ.

(* 若一致集都是可满足的, 那么完备性定理成立! *)
Lemma complete_consistence_satisfiable : consistence_satisfiable -> complete.
Proof.
  red; intros. red in H. pose proof H (Γ ∪ [/¬p]).
  destruct (classic (Γ ├ p)); auto. apply consistence_contra in H2.
  apply H1 in H2. apply satisfiable_contra in H2. tauto.
Qed.

(* (*极大一致集：一致集Γ，对任意p不属于Γ, 都有Γ∪[/ p]不是一致的*)
Definition max_consistence (Γ:Ensemble(Formula)) :=
  consistence Γ /\ (forall p, ~ p∈Γ -> ~ consistence (Γ∪[/ p])). *)
(* (* 极大一致集 *)
Definition maximal_consistent_set Γ := 
  consistence Γ /\ forall p, consistence (Γ ∪ [/p]) -> p ∈ Γ. *)
(*极大一致集的另一种定义*)

(* Definition max_consistence' Γ := 
  consistence Γ /\ (forall p, consistence (Γ ∪ [/p]) -> p ∈ Γ ).

(* 两种极大一致集等价 *)
Fact max_consistence_eq : forall Γ, 
  maximal_consistent_set Γ <-> max_consistence' Γ.
Proof.
  split; intros.
  - red in *. destruct H. split; auto.
  - red in *. destruct H. split; auto.
Qed. *)


(* 极大一致集 *)
Definition maximal_consistent_set Γ := 
  consistence Γ /\ forall p, consistence (Γ ∪ [/p]) -> p ∈ Γ.

(* 极大一致集的基本性质 *)
(* 极大一致集Γ, Γ├p -> p∈Γ *)
Fact max_consistence_fact1 : forall Γ, maximal_consistent_set Γ
  -> forall p, Γ ├ p -> p ∈ Γ.
Proof.
  intros. destruct H. destruct (classic (p ∈ Γ)); auto.
  assert (forall p, ~ p ∈ Γ -> ~ consistence (Γ ∪ [/p])) as H1a.
    { intros. intro; auto. }
  apply H1a in H2. destruct H2. red. intros. intro. destruct H2.
  pose proof rule_Reduction_absurdity _ _ _ H2 H3. destruct (H p); tauto.
Qed.

(* 极大一致集Γ, ¬p∈Γ当且仅当p∉Γ *)
Fact max_consistence_fact2 : forall Γ, maximal_consistent_set Γ
  -> forall p, ¬p ∈ Γ <-> ~ p ∈ Γ.
Proof.
  intros. split; intros.
  - intro. destruct H. red in H. apply H with p. split; autoK.
  - pose proof H as MX. destruct H.
    assert (forall p, ~ p ∈ Γ -> ~ consistence (Γ ∪ [/p])) as H1a.
      { intros. intro; auto. }
    apply H1a in H0. red in H. unfold consistence in H0. 
    apply not_all_not_ex in H0. destruct H0 as [q []].
    pose proof rule_Reduction_absurdity _ _ _ H0 H2.
    apply max_consistence_fact1; auto.
Qed.

(* 极大一致集Γ, (p→q)∈Γ当且仅当~p∈Γ或q∈Γ *)
Fact max_consistence_fact3 : forall Γ p q, maximal_consistent_set Γ
  -> ((p → q) ∈ Γ <-> (¬p ∈ Γ \/ q ∈ Γ)).
Proof.
  intros Γ p q H. split; intros.
  - destruct (classic (q ∈ Γ)); auto. left; auto.
    apply (max_consistence_fact2 _ H) in H1. apply (max_consistence_fact2 _ H).
    intro. assert(Γ ├ p). { autoK. } assert(Γ ├ q). { autoK. }
    assert(Γ ├ ¬q). { constructor. auto. }
    destruct H as [H H6]. pose proof H q. destruct H7. auto. 
  - destruct H0.
    + destruct (classic (q ∈ Γ)).
      * assert (Γ ├ q) by autoK. assert (Γ ├ p → q). { eapply MP; eauto. autoK. }
        apply max_consistence_fact1 in H3; auto.
      * apply max_consistence_fact2 in H1; auto.
        assert (Γ ├ ¬p). { constructor. auto. }
        assert (Γ ├ ¬q). { constructor. auto. } assert (Γ ├ ¬q → ¬p) by autoK.
        assert (Γ ├ (¬ q → ¬ p) → p → q). { apply L3. }
        apply max_consistence_fact1; auto. eapply MP; eauto.
    + assert (Γ ├ q) by autoK. assert (Γ ├ p → q). { eapply MP; eauto. autoK. }
      apply max_consistence_fact1; auto.
Qed.

(* 可满足定理 *)

(* 亨金证据 *)
(* 见证性Witness Property: Γ是一致集, 对任意p, 变元x, 若(¬(Forall x p)) ∈ Γ, 
   则存在c∈Con, 使得 ¬(p(c/x))∈Γ *)
Definition witness_property Γ := forall p x, (¬(∀ x, p)) ∈ Γ
  -> exists c, (¬(substitute_f p (Tcon c) x)) ∈ Γ.

(* 具有witness property的极大一致集存在模型(存在MM,v使得{MM;v}|=Γ) *)
Definition model_existence := forall Γ, maximal_consistent_set Γ 
  -> witness_property Γ -> exists MM v, satisfyable MM v Γ.

(* 可满足的: 若存在模型(MM,v)使得{MM; v} |= p 对每个 p∈Γ 都成立*)
Definition satisfiable Γ := exists MM v, satisfyable MM v Γ.
(* 已定义 (* Γ可满足 *)
  Definition satisfyable_Γ Γ := exists MM v, satisfyable MM v Γ. *)

(* 下面这个Section证明：具有亨金证据的极大一致集存在模型 *)
(* 下面这个Section证明：具有witness property的极大一致集存在模型 *)
Section model_existence_proof.
Variable Γ : Ensemble(Formula).
Hypothesis H1 : maximal_consistent_set Γ.
Hypothesis H2 : witness_property Γ.

(* 定义两个项满足等词关系 *)
Definition term_equality_relation : term -> term -> Prop :=
  fun t1 t2 => (equality t1 t2) ∈ Γ.

(* 等词关系满足自反性 *)
Fact term_equality_relation_refl : reflexive _ term_equality_relation.
Proof.
  unfold reflexive, term_equality_relation. intro t. 
  apply max_consistence_fact1; auto. apply K1. apply E1.
Qed.

(* 等词关系满足对称性 *)
Fact term_equality_relation_sym : symmetric _ term_equality_relation.
Proof.
  unfold symmetric, term_equality_relation. intros t1 t2 H.
  apply max_consistence_fact1; auto. apply MP with (equality t1 t2).
  - apply K1. apply E2.
  - apply K0. auto.
Qed.

(* 等词关系满足传递性 *)
Fact term_equality_relation_tran : transitive _ term_equality_relation.
Proof.
  unfold transitive, term_equality_relation. intros t1 t2 t3 H3 H4.
  apply max_consistence_fact1; auto. apply MP with (equality t2 t3).
  - apply MP with (equality t1 t2).
    + apply K1. apply E3.
    + apply K0. auto.
  - apply K0. auto.
Qed.

(* 等词关系满足等价关系 *)
Fact term_equality_relation_equiv : equivalence _ term_equality_relation.
Proof.
  split.
  - apply term_equality_relation_refl.
  - apply term_equality_relation_tran.
  - apply term_equality_relation_sym.
Qed.

(* 定义项的等价类的集族 *)
Inductive term_equality_relation_family : (term -> Prop) -> Prop := 
  | term_equality_relation_family_intro : forall t,
      term_equality_relation_family (term_equality_relation t).

(* 等价类的非空性 *)
Fact inhabit_tecf : forall A, term_equality_relation_family A -> exists x, A x.
Proof.
  intros. destruct H. exists t. red. apply term_equality_relation_refl.
Qed.

(* 定义论域类型 *)
Definition domain := sig term_equality_relation_family.
Print sig.

Fact projection_injective_domain :
  forall t1 t2: domain, proj1_sig t1 = proj1_sig t2 -> t1 = t2.
Proof.
  intros. destruct t1, t2. simpl in *. subst. f_equal. apply proof_irrelevance.
Qed.
Print proj1_sig.

(* 定义论域的元素 *)
Definition term_domain (t: term) : domain :=
  exist _ (term_equality_relation t) (term_equality_relation_family_intro t).

(* 若term_equality_relation t t0, 
   则term_equality_relation t = term_equality_relation t0*)
Fact eq_term_set : forall t t0, term_equality_relation t t0 
  -> term_equality_relation t = term_equality_relation t0.
Proof.
  intros. apply Extensionality_Ensembles. split; red; intros.
  - red in H0; red. apply term_equality_relation_sym.
    apply term_equality_relation_sym in H0.
    apply term_equality_relation_tran with t; auto.
  - red in H0; red. apply term_equality_relation_tran with t0; auto.
Qed.

Fact term_equality_relation_family_intro_equiv : forall t t0,
  term_equality_relation t = term_equality_relation t0 
  -> term_equality_relation_family (term_equality_relation t) 
       = term_equality_relation_family (term_equality_relation t0).
Proof. intros. f_equal. auto. Qed.

Fact eq_term_to_domain : forall t t0, term_equality_relation t t0
  -> term_domain t = term_domain t0.
Proof.
  intros. pose proof eq_term_set _ _ H.
  pose proof term_equality_relation_family_intro_equiv _ _ H0.
  unfold term_domain. apply projection_injective_domain. simpl. auto.
Qed.

Fact eq_domain_to_term : forall t t0, term_domain t = term_domain t0
  -> term_equality_relation t t0.
Proof.
  intros. unfold term_domain in H. inversion H. rewrite H3.
  apply term_equality_relation_refl.
Qed.

(* 定义I_c *)
Definition Ic (c: Con) : domain := term_domain (Tcon c).

(* Check @ Vector.map. *)

(* pick函数: 从存在性证明中提取元素 *)
Definition pick {A} {P : A -> Prop} (l : exists x, P x) :=
  proj1_sig (constructive_indefinite_description _ l).

(* 将项的等价类类型转化为term类型 *)
Definition domain_term (d: domain) : term.
  destruct d as [d Hd]. pose proof inhabit_tecf d. apply H in Hd.
  refine (pick _). apply Hd.
Defined.

(* Check @ map. *)

(* 定义I_f *)
Definition If (f: Fun) (v: Vector.t domain (arity_F f)) : domain :=
  term_domain (Tfun f (Vector.map domain_term v)).

(* 定义I_R *)
Definition IR (r: Rel) (v: Vector.t domain (arity_R r)) : Prop :=
  (atomic r (Vector.map domain_term v)) ∈ Γ.

(* 辅助引理：equality_4的性质 *)
Lemma equality_4_apply : forall (r: Formula) (m: nat) (v1 v2: Vector.t term m),
  Γ ├ equality_4 r m m v1 v2 -> Forall2 (fun t1 t2 => (equality t1 t2) ∈ Γ) v1 v2
  -> Γ ├ r.
Proof.
  intros r m v1. revert r. induction v1; intros r v2 H HForall.
  - (* 空向量情况 *)
    simpl in H. auto.
  - (* cons情况 *)
    dependent destruction v2. dependent destruction HForall. simpl in H. 
    eapply IHv1.
    + eapply MP; [apply H | apply K0; apply H0].
    + apply HForall.
Qed.

(* 对于任意n元函数符号f, 任意项s1、s2、……、sn, t1、t2、……、tn, 
   如果对任意i, si和ti满足等词关系, 
   那么f(s1, s2, ……, sn)和f(t1, t2, …… ,tn)满足等词关系 *)
Lemma If_equality' : forall f (v1 v2: Vector.t term (arity_F f)),
  Forall2 (fun t1 t2 => term_equality_relation t1 t2) v1 v2 
  -> term_equality_relation (Tfun f v1) (Tfun f v2).
Proof.
  intros f v1 v2 H. unfold term_equality_relation.
  (* 使用max_consistence_fact1 *)
  apply max_consistence_fact1; auto.
  (* 应用E5公理 *)
  pose proof (K1 Γ (equality_4 (equality (Tfun f v1) (Tfun f v2))
                     (arity_F f) (arity_F f) v1 v2) (E5 f v1 v2)).
  (* 使用equality_4_apply *)
  eapply equality_4_apply; eauto.
Qed.

Check Forall2.

(* 向量版本的Forall2对称性引理 *)
Lemma Forall2_vec_sym : forall {A n} (R: A -> A -> Prop) (v1 v2: Vector.t A n),
  (forall x y, R x y -> R y x) -> Forall2 R v1 v2 -> Forall2 R v2 v1.
Proof.
  intros A n R v1. induction v1; intros v2 Hsym HF.
  - dependent destruction v2. constructor.
  - dependent destruction v2. dependent destruction HF. constructor.
    + apply Hsym. auto.
    + apply IHv1; auto.
Qed.

(* 辅助引理: 将Forall2 term_equality_relation转换为Forall2 (equality ... ∈ Γ) *)
Lemma Forall2_term_eq_to_in_Gamma : forall {n} (v1 v2: Vector.t term n),
  Forall2 (fun t1 t2 => term_equality_relation t1 t2) v1 v2
  -> Forall2 (fun t1 t2 => (equality t1 t2) ∈ Γ) v1 v2.
Proof.
  intros n v1. induction v1; intros v2 HF.
  - dependent destruction v2. constructor.
  - dependent destruction v2. dependent destruction HF. constructor.
    + unfold term_equality_relation in HF. auto.
    + apply IHv1. auto.
Qed.

(* 对于任意n元关系符号r, 任意项s1、s2、……、sn, t1、t2、……、tn, 
   如果对任意i, 有si和ti满足等词关系, 
   那么r(s1, s2, ……, sn)∈Γ当且仅当r(t1, t2, …… ,tn)∈Γ *)
Lemma IR_equality' : forall r (v1 v2: Vector.t term (arity_R r)),
  Forall2 (fun t1 t2 => term_equality_relation t1 t2) v1 v2
  -> (atomic r v1) ∈ Γ <-> (atomic r v2) ∈ Γ.
Proof.
  intros r v1 v2 H.
  split; intros.
  - (* 正向：atomic r v1 ∈ Γ -> atomic r v2 ∈ Γ *) (* 转换Forall2 *)
    pose proof (Forall2_term_eq_to_in_Gamma v1 v2 H) as HForall.
    (* 应用E4公理 *)
    pose proof (K1 Γ (equality_4 (atomic r v1 → atomic r v2) 
                       (arity_R r) (arity_R r) v1 v2) (E4 r v1 v2)) as HE4.
    (* 使用equality_4_apply得到蕴含式 *)
    assert (Γ ├ atomic r v1 → atomic r v2) as Himpl.
      { eapply equality_4_apply; eauto. }
    (* 应用MP规则 *)
    assert (Γ ├ atomic r v2) as Hderive.
      { eapply MP.
        - apply Himpl.
        - apply K0. auto. }
    (* 使用max_consistence_fact1 *)
    apply max_consistence_fact1; auto.
  - (* 反向：atomic r v2 ∈ Γ -> atomic r v1 ∈ Γ *) (* 利用等词关系的对称性 *)
    assert(HForall_rev: Forall2 (fun t1 t2 => term_equality_relation t1 t2) v2 v1).
      { apply Forall2_vec_sym; auto.
        intros. apply term_equality_relation_sym. auto. }
    (* 转换Forall2 *)
    pose proof (Forall2_term_eq_to_in_Gamma v2 v1 HForall_rev) as HForall.
    (* 应用E4公理(v2到v1方向) *)
    pose proof (K1 Γ (equality_4 (atomic r v2 → atomic r v1) 
                       (arity_R r) (arity_R r) v2 v1) (E4 r v2 v1)) as HE4.
    (* 使用equality_4_apply得到蕴含式 *)
    assert (Γ ├ atomic r v2 → atomic r v1) as Himpl.
      { eapply equality_4_apply; eauto. }
    (* 应用MP规则 *)
    assert (Γ ├ atomic r v1) as Hderive.
      { eapply MP.
        - apply Himpl.
        - apply K0. auto. }
    (* 使用max_consistence_fact1 *)
    apply max_consistence_fact1; auto.
Qed.

(* 结构(domain,I) *)
Definition D_I : Module := {|
  M := domain;
  I_c := Ic;
  I_f := If;
  I_R := IR |}.

(* 定义指派 *)
Definition assignment (x: Var) : @ M D_I.
  simpl. apply term_domain. exact (Tvar x).
Defined.

Fact inv_domain_term : forall t,
  term_equality_relation (domain_term (term_domain t)) t.
Proof.
  intros. red. unfold term_domain. unfold domain_term.
  unfold pick. destruct constructive_indefinite_description. simpl.
  red in t0. apply term_equality_relation_sym. auto.
Qed.

(* 项向量v, 有Vector.map (assignment //) v = Vector.map term_domain v *)
(* Check @ map. *)
Definition assignment_v (n: nat) (v: Vector.t (term) n) :=
  Vector.map (assignment //) v = Vector.map term_domain v.

(* 任意项t, 有(assignment) // t = term_domain t *)
Lemma assignment_t : forall t, assignment // t = term_domain t.
Proof.
  apply Term_ind_new with assignment_v.
  - simpl. intros. unfold assignment. auto.
  - simpl. unfold Ic. auto.
  - red. intros. apply case0.
    set (fun x => Vector.map ((assignment) //) x = nil domain) as P.
    apply (case0 P). unfold P. simpl. auto.
  - intros. simpl. unfold If. simpl. rewrite H. apply eq_term_to_domain.
    apply If_equality'. destruct f. simpl in *. induction v.
    + simpl. constructor.
    + apply Forall2_cons.
      * apply inv_domain_term.
      * apply IHv. red in H. simpl in H. apply cons_inj in H. 
        destruct H. red. auto.
  - intros. red. simpl. f_equal; auto.
Qed.

Check @ cons_inj.

Lemma assignment_v' : forall n v, assignment_v n v.
Proof.
  intros. red. induction v.
  - simpl. auto.
  - simpl. repeat rewrite -> assignment_t. f_equal; auto.
Qed.

(* 辅助引理：常元对任意公式都是自由的 *)
Lemma t_x_free_const : forall p c v, t_x_free p (Tcon c) v = true.
Proof.
  induction p; simpl; auto.
  - (* Contain 情况 *)
    intros. rewrite IHp1, IHp2. auto.
  - (* ForAll 情况 *)
    intros. destruct (classicT (v ∈ (Formula_free_Ens (ForAll v0 p)))).
    + destruct (classicT (v0 ∈ (term_Ens (Tcon c)))).
      * (* 常元的变元集是空集, 矛盾 *)
        simpl in i. destruct i. simpl in *. destruct i0.
      * simpl in *. destruct (classicT (v ∈ Φ_Vr)); auto.
        destruct i0. rewrite IHp. destruct classicT; auto.
    + simpl in *. destruct (classicT (v ∈ Φ_Vr)); auto.
      destruct i. rewrite IHp. destruct classicT; auto.
Qed.

(* 辅助引理：assignment 在常元上的值 *)
Lemma assignment_const : forall c, assignment // (Tcon c) = Ic c.
Proof. intros. simpl. unfold Ic. reflexivity. Qed.

(* 辅助引理：从 domain 提取对应的项 *)
Lemma domain_has_term : forall (m : domain), exists t, m = term_domain t.
Proof.
  intros [m_set Hm_set]. destruct Hm_set as [t]. exists t. unfold term_domain.
  apply projection_injective_domain. simpl. reflexivity.
Qed.

(* (equality t t0) ∈ Γ -> {D_I; assignment}|= (equality t t0) *)
Lemma model_satisfiable_le1' : forall t t0, 
  (equality t t0) ∈ Γ -> satisfy_R D_I assignment (equality t t0).
Proof.
  intros. assert(term_equality_relation t t0); auto.
  assert (term_equality_relation t = term_equality_relation t0).
    { apply Extensionality_Ensembles. split; red; intros.
      - red. red in H3. unfold term_equality_relation in *.
        apply term_equality_relation_sym in H0.
        apply term_equality_relation_tran with t; auto.
      - red. red in H3. unfold term_equality_relation in *.
        apply term_equality_relation_tran with t0; auto. }
  simpl. rewrite assignment_t. rewrite assignment_t. 
  apply eq_term_to_domain; auto.
Qed.

Lemma model_satisfiable_le1 : forall t t0, 
  (equality t t0) ∈ Γ <-> satisfy_R D_I assignment (equality t t0).
Proof.
  split; intros.
  - apply model_satisfiable_le1'; auto.
  - red in H. do 2 rewrite assignment_t in H.
    apply eq_domain_to_term in H; auto.
Qed.

Lemma model_satisfiable_le2' : forall r (s : t term (arity_R r)), 
  (atomic r s) ∈ Γ -> satisfy_R D_I assignment (atomic r s).
Proof.
  intros. simpl. unfold IR. rewrite assignment_v'.
  pose proof IR_equality' r s (map domain_term (map term_domain s)).
  apply H0; auto. clear H0. rewrite map_map. destruct r. simpl in *.
  clear H. induction s.
  - constructor.
  - apply Forall2_cons.
    + unfold pick. destruct constructive_indefinite_description. simpl; auto.
    + apply IHs.
Qed.

Lemma model_satisfiable_le2 : forall r (s : t term (arity_R r)), 
  (atomic r s) ∈ Γ <-> satisfy_R D_I assignment (atomic r s).
Proof.
  split; intros.
  - apply model_satisfiable_le2'; auto.
  - red in H. unfold I_R in H. simpl in *. red in H. rewrite assignment_v' in H.
    pose proof IR_equality' r s (map domain_term (map term_domain s)).
    apply H0; auto. clear H0. rewrite map_map. destruct r; simpl in *.
    clear H. induction s.
    + constructor.
    + apply Forall2_cons.
      * unfold pick. destruct constructive_indefinite_description. simpl; auto.
      * apply IHs.
Qed.

Lemma model_satisfiable_le3 : forall p, (p ∈ Γ <-> {D_I; assignment}|= (p))
  -> ¬p ∈ Γ <-> {D_I; assignment} |= (¬p).
Proof.
  intros. destruct (classic (p ∈ Γ)).
  - destruct H1. red in H4. split; intros.
    + destruct (H3 p); split; constructor; auto.
    + simpl in H5. rewrite H in H0; tauto.
  - destruct H1. split; intros.
    + simpl. intro. rewrite <- H in H6; tauto.
    + apply max_consistence_fact2; auto.
Qed.

Lemma model_satisfiable_le4 : forall p1 p2, (p1 ∈ Γ <-> {D_I; assignment}|= p1) 
  -> (p2 ∈ Γ <-> {D_I; assignment} |= p2)
  -> ((p1 → p2) ∈ Γ <-> {D_I; assignment}|= (p1 → p2)).
Proof.
  split; intros.
  - simpl. apply max_consistence_fact3 in H3; auto. destruct H3.
    + left. intro. apply max_consistence_fact2 in H3; auto.
      rewrite <-H in H4; auto.
    + right. apply H0; auto.
  - simpl in H3. apply max_consistence_fact3; auto. destruct H3.
    + left. apply max_consistence_fact2; auto. intro. rewrite H in H4; auto.
    + right. rewrite H0; auto.
Qed.

(* 定义公式的复杂度(逻辑深度) *)
Fixpoint formula_complexity (p: Formula) : nat :=
  match p with
  | equality _ _ => 0
  | atomic _ _ => 0
  | Not q => S (formula_complexity q)
  | Contain q r => S (max (formula_complexity q) (formula_complexity r))
  | ForAll _ q => S (formula_complexity q)
  end.

(* 辅助引理：替换不增加复杂度 *)
Fact subst_complexity : forall p t v,
  formula_complexity (substitute_f p t v) <= formula_complexity p.
Proof.
  induction p; simpl; intros.
  - lia.
  - lia.
  - specialize (IHp t v). lia.
  - specialize (IHp1 t v). specialize (IHp2 t v). lia. 
  - destruct (eqbv v v0); simpl.
    + bdestruct (eqbv v0 v); subst. simpl; lia. simpl. pose proof IHp t v0. lia.
    + bdestruct (eqbv v0 v); subst. simpl; lia. simpl. pose proof IHp t v0. lia.
Qed.


(* 辅助引理1: 证明 Γ ⊢ (t = t) *)
Lemma derive_eq_refl : forall t, Γ ├ equality t t.
Proof. intros. apply K1. apply E1. Qed.

(* 辅助引理2: 从 Γ ⊢ p 得到 p ∈ Γ(极大一致性) *)
(* 这就是 max_consistence_fact1. *)

(* 辅助引理3: 证明 Γ ⊢ ¬(t = t) → ⊥(矛盾式) *)
Lemma derive_eq_not_false : forall t, Γ ├ (¬(equality t t)) → (¬(equality t t)).
Proof. intros. apply law_identity. Qed.

(* 辅助引理4：从 ¬¬p ∈ Γ 得到 p ∈ Γ *)
Lemma double_neg_in_max_consistence : forall p, (¬¬p) ∈ Γ -> p ∈ Γ.
Proof.
  intros. apply max_consistence_fact1; auto. apply MP with (¬¬p).
  - apply law_double_negation.
  - apply K0. auto.
Qed.

(* 找到项中最大的变元编号 *)
Fixpoint max_var_in_term (t : term) : nat :=
  match t with
  | Tcon _ => 0
  | Tvar (X n) => n
  | Tfun _ v => 
      let fix max_var_in_vector {n} (vec : Vector.t term n) : nat :=
        match vec with
        | [] => 0
        | h :: tail => max (max_var_in_term h) (max_var_in_vector tail)
        end
      in max_var_in_vector v
  end.

(* 提取向量中的最大变元编号 *)
Fixpoint max_var_in_vector {n} (vec : Vector.t term n) : nat :=
  match vec with
  | [] => 0
  | h :: tail => max (max_var_in_term h) (max_var_in_vector tail)
  end.

(* 选择一个新的变元 *)
Definition fresh_var (t : term) : Var := X (S (max_var_in_term t)).

(* 辅助引理：如果 X n ∈ term_Ens t, 则 n <= max_var_in_term t *)
Lemma var_in_term_le_max : forall t n, (X n) ∈ (term_Ens t)
  -> n <= max_var_in_term t.
Proof.
  intros t. 
  apply Term_ind_new with 
    (P := fun t => forall n, (X n) ∈ (term_Ens t) -> n <= max_var_in_term t)
    (P0 := fun m vec => forall n, (X n) ∈ (Vector_Ens m vec) 
                        -> n <= max_var_in_vector vec).
  - (* Tvar 情况 *)
    intros m n. simpl. intros H. apply Single in H. inversion H. subst. lia.
  - (* Tcon 情况 *)
    intros c n. simpl. intros H. destruct H.
  - (* 空向量 *)
    intros s n H.
    apply (case0 (fun v => (X n) ∈ (Vector_Ens 0 v) -> n <= max_var_in_vector v)).
    simpl. intros. inversion H0. auto.
  - (* Tfun 情况 *)
    intros f v IHv n. simpl. apply IHv.
  - (* cons 情况 *)
    intros m s t0 IHs IHt0 n. simpl. intros H. apply UnionI in H. destruct H.
    + specialize (IHs n H). lia.
    + specialize (IHt0 n H). lia.
Qed.

(* 主引理：新的变元不在项中 *)
Lemma fresh_var_not_in : forall t, ~ (fresh_var t) ∈ (term_Ens t).
Proof.
  intros t. unfold fresh_var. intro H. apply var_in_term_le_max in H.
  simpl in H. lia.
Qed.

(* 主引理：对任意项 t，存在常元 c 使得 (c = t) ∈ Γ *)
Lemma exist_const_for_term : forall t, exists c, (equality (Tcon c) t) ∈ Γ.
Proof.
  intros t.
  (* 选择一个不在 t 中出现的变元 *)
  (* 简单起见, 我们假设存在这样的变元 *)
  (* 实际上, 可以取一个足够大的编号 *)
  remember (fresh_var t) as y. remember (¬(equality (Tvar y) t)) as phi.
  (* 关键: 我们需要分情况讨论y是否在t中 *)
  destruct (classic (y ∈ (term_Ens t))).
  - (* 情况1：y ∈ term_Ens t 矛盾 *)
    pose proof fresh_var_not_in t. elim H0. subst; auto.
  - (* 情况2: y ∉ term_Ens t *)
    (* 这是主要情况 *)
    (* 证明 ¬(∀ y, phi) ∈ Γ *)
    assert (Hneg_forall: ¬(∀ y, phi) ∈ Γ).
    { apply max_consistence_fact1; auto.
      (* 使用演绎定理 *)
      (* 现在需要从 Γ ∪ [/∀ y, phi] 推导矛盾 *)
      (* 即推导出 (equality t t) 和 ¬(equality t t) *)
      (* 首先推导 ¬(equality t t) *)
      assert (Hneg_eq: (Γ ∪ [/∀ y, phi]) ├ ¬(equality t t)).
      { (* 从 ∀ y, phi 实例化 *)
        assert (Ht_free: t_x_free phi t y = true).
        { subst phi y. simpl. destruct (classicT 
            (X 0 ∈ (Formula_free_Ens (¬(equality (Tvar (X 0)) t))))).
          - simpl in i. destruct i; auto.
          - auto. }
        (* 应用 S' 公理 *)
        assert (Hinst: (Γ ∪ [/∀ y, phi]) ├ (∀ y, phi) → substitute_f phi t y).
        { apply K1. apply S'. exact Ht_free. }
        (* 从 ∀ y, phi ∈ (Γ ∪ [/∀ y, phi]) *)
        assert (Hforall: (Γ ∪ [/∀ y, phi]) ├ ∀ y, phi).
        { apply K0. right. split. }
        (* 应用 MP *)
        assert (Hsubst: (Γ ∪ [/∀ y, phi]) ├ substitute_f phi t y).
        { apply MP with (∀ y, phi); auto. }
        (* 化简 substitute_f phi t y *)
        assert (Heq_subst: substitute_f phi t y = ¬(equality t t)).
        { subst phi y. simpl. f_equal. f_equal.
          bdestruct (max_var_in_term t =? max_var_in_term t); auto.
          destruct H0; lia. pose proof subst_term_ignore. apply H0; auto. }
        rewrite Heq_subst in Hsubst. exact Hsubst. }
      (* 然后推导 equality t t *)
      assert (Heq: (Γ ∪ [/∀ y, phi]) ├ equality t t).
      { apply Union_l. apply K1. apply E1. }
      (* 产生矛盾 *)
      apply MP with (equality t t); autoK.
      pose proof rule_Reduction_absurdity _ _ _ Heq Hneg_eq. autoK. (*显然*) }
    (* 应用 witness property *)
    specialize (H2 phi y Hneg_forall). destruct H2 as [c Hc].
    (* 化简 substitute_f phi (Tcon c) y *)
    assert (Hsubst_c: substitute_f phi (Tcon c) y = ¬(equality (Tcon c) t)).
    { subst phi y. simpl. pose proof subst_term_ignore. f_equal. f_equal.
      bdestruct (max_var_in_term t =? max_var_in_term t); auto.
      destruct H3; lia. apply H0; auto. }
    rewrite Hsubst_c in Hc.
    (* Hc : (¬¬equality (Tcon c) t)) ∈ Γ *)
    (* 应用双重否定消去 *)
    exists c. apply double_neg_in_max_consistence. exact Hc.
Qed.

(* 推论：Ic c 和 term_domain t 在 domain 中相等 *)
Corollary exist_const_for_domain : forall t, exists c, Ic c = term_domain t.
Proof.
  intros t. destruct (exist_const_for_term t) as [c Hc]. exists c. unfold Ic.
  apply eq_term_to_domain. unfold term_equality_relation. exact Hc.
Qed.

(* 主引理：对给定复杂度的所有公式证明 model_sat *)
Lemma model_sat_complexity : forall n p, formula_complexity p <= n
  -> p ∈ Γ <-> {D_I; assignment} |= p.
Proof.
  induction n; intros p Hcomp.
  - (* Base case: n = 0 *)
    destruct p; simpl in Hcomp; try lia.
    + apply model_satisfiable_le1.
    + apply model_satisfiable_le2.
  - (* Inductive case: n = S n *)
    destruct p; simpl in Hcomp.
    + apply model_satisfiable_le1.
    + apply model_satisfiable_le2.
    + (* Not case *)
      apply model_satisfiable_le3. apply IHn. simpl in Hcomp. lia.
    + (* Contain case - 对应 Conjunction *)
      apply model_satisfiable_le4.
      * apply IHn. simpl in Hcomp. lia.
      * apply IHn. simpl in Hcomp. lia.
    + (* ForAll case *)
      split; intros.
      * (* 正向: ∀v, p ∈ Γ -> {D_I; assignment} |= ∀v, p *)
        simpl. intros m.
        (* 步骤1: 从 m ∈ domain 提取对应的项 t *)
        destruct (domain_has_term m) as [t Ht]. subst m.
        (* 现在 m = term_domain t，即 m = t^~ *)
        (* 步骤2: 我们需要找到常元 c 使得 c^~ = t^~ = term_domain t *)
        assert (Hexist_c: exists c, Ic c = term_domain t).
        { apply exist_const_for_domain. } 
        destruct Hexist_c as [c Hc].
        (* 步骤3: 从 ∀v, p ∈ Γ 推导 p[c/v] ∈ Γ *)
        assert (Ht_free: t_x_free p (Tcon c) v = true). 
        { apply t_x_free_const. }
        assert (Hderiv: Γ ├ substitute_f p (Tcon c) v).
        { apply MP with (∀ v, p).
          - apply K1. apply S'. apply Ht_free.
          - apply K0. auto. }
        assert (Hsubst_in: substitute_f p (Tcon c) v ∈ Γ).
        { apply max_consistence_fact1; auto. }
        (* 步骤4: 使用归纳假设 *)
        assert (Hcomp_subst: formula_complexity (substitute_f p (Tcon c) v) <= n).
        { pose proof (subst_complexity p (Tcon c) v). simpl in Hcomp. lia. }
        apply IHn in Hcomp_subst. rewrite Hcomp_subst in Hsubst_in.
        (* 现在有：{D_I; assignment} ⊨ p[c/v] *)
        (* 步骤5: 应用替换定理 *)
        pose proof 
          (formula_substitution_theorem D_I p (Tcon c) v Ht_free assignment).
        destruct H0. apply H0 in Hsubst_in.
        (* 现在有：{D_I; assignment[v |-> assignment//(Tcon c)]} ⊨ p *)
        (* 步骤6: 证明 assignment // (Tcon c) = Ic c = term_domain t *)
        rewrite assignment_const in Hsubst_in. rewrite Hc in Hsubst_in.
        exact Hsubst_in.
      * (* 反向: {D_I; assignment} |= ∀v, p -> ∀v, p ∈ Γ *)
        (* 反证法: 假设 ∀v, p ∉ Γ *)
        destruct (classic (∀ v, p ∈ Γ)); auto.
        (* 由极大一致性, ¬∀v, p ∈ Γ *)
        apply max_consistence_fact2 in H0; auto.
        (* 由 witness property, 存在常元 c 使得 ¬p[c/v] ∈ Γ *)
        unfold witness_property in H2. specialize (H2 p v H0).
        destruct H2 as [c Hc].
        (* 由极大一致性引理，p[c/v] ∉ Γ *)
        assert (Hnotin: ~ substitute_f p (Tcon c) v ∈ Γ).
        { apply max_consistence_fact2 in Hc; auto. }
        (* 由归纳假设，{D_I; assignment} |≠ p[c/v] *)
        assert (Hcomp_subst: formula_complexity (substitute_f p (Tcon c) v) <= n).
        { pose proof (subst_complexity p (Tcon c) v). simpl in Hcomp. lia. }
        apply IHn in Hcomp_subst. rewrite Hcomp_subst in Hnotin.
        (* 由替换定理和 assignment_const *)
        assert (Ht_free: t_x_free p (Tcon c) v = true). { apply t_x_free_const. }
        pose proof 
          (formula_substitution_theorem D_I p (Tcon c) v Ht_free assignment).
        destruct H1.
        (* 从假设 {D_I; assignment} |= ∀v, p，特化到 Ic c *)
        simpl in H. specialize (H (Ic c)). tauto.
Qed.

(* 主引理：{D_I; assignment} |= Γ 作为 model_sat_complexity 的推论 *)
Lemma model_sat : forall p, p ∈ Γ <-> {D_I; assignment} |= p.
Proof.
  intro p. apply model_sat_complexity with (n := formula_complexity p). lia.
Qed.

(* 可满足定理 *)
Theorem satisfiable_theorem : satisfiable Γ.
Proof. red. exists D_I. exists assignment. red. apply model_sat. Qed.

End model_existence_proof.


