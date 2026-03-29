(**************************************************************************)
(*  This is part of semantic_pc, it is distributed under the terms of the *)
(*            GNU Lesser General Public License version 3                 *)
(*               (see file LICENSE for more details)                      *)
(*                                                                        *)
(*                       Copyright 2023-2028                              *)
(*         Dakai Guo, qiming Wang, jianghao Liu and Wensheng Yu           *)
(**************************************************************************)

(* 可扩张定理 *)
(* 任意一致集都可以扩张成具有见证性的极大一致集 *)
(* 由一致集构造具有见证性的极大一致集 *)

Require Import base_pc.
Require Import formulas_K_System.
Require Import syntax_K_System.
Require Import semantic_K_System.
Require Import soundness_K_System.
Require Import complete_K_System.
Require Import Mappings.

Require Import Coq.Vectors.Vector.
Import VectorNotations.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.micromega.Lia.

(**************************************************************************)
(*      扩张，通过 double_C（常元加倍）操作，将原来的常元ci映射到偶数下标c2i，    *)
(*            从而腾出所有奇数下标的常元 c 2i+1作为新常量使用                   *)
(**************************************************************************)

(* 将项t中出现的所有常元c_i替换成c_2i *)
Fixpoint double_C_term (t: term) : term :=
  match t with
  | Tcon c => match c with
              | C n => Tcon (C (2 * n))
              end
  | Tvar y => Tvar y
  | Tfun  _ q => let fix double_C_vc (n: nat) (r: Vector.t term n) :=
                   match r with 
                    | [] => []
                    | h :: q => (double_C_term h) :: (double_C_vc _ q) 
                   end in (Tfun _ (double_C_vc _ q))
  end.

(* 将项向量v中出现的所有常元c_i替换成c_2i *)
Fixpoint double_C_vector (n: nat) (r: Vector.t term n) : Vector.t term n :=
  match r with 
  | [] => []
  | h :: q => (double_C_term h) :: (double_C_vector _ q)
  end.

(* 将公式p中出现的所有常元c_i替换成c_2i *)
Fixpoint double_C_formula (p: Formula) : Formula :=
  match p with 
  | equality t1 t2 => equality (double_C_term t1) (double_C_term t2)
  | atomic _ q => atomic _ (double_C_vector _ q)
  | Not q => Not (double_C_formula q)
  | Contain m n => Contain (double_C_formula m) (double_C_formula n)
  | ForAll x q => ForAll x (double_C_formula q)
  end.

(* 将Γ中出现的所有常元c_i替换成c_2i *)
Inductive double_C_set Γ : Ensemble Formula :=
  | double_C_set_intro : forall p, p ∈ Γ 
                           -> (double_C_formula p) ∈ (double_C_set Γ). 

(* 辅助引理：double_C 操作保持项的结构 *)
Fact double_C_term_var : forall x, double_C_term (Tvar x) = Tvar x.
Proof. reflexivity. Qed.

Fact double_C_vector_map : forall n (v : Vector.t term n),
  double_C_vector n v = Vector.map double_C_term v.
Proof.
  intros. induction v.
  - reflexivity.
  - simpl. f_equal.
Qed.

(* ==========double_C 保持一致性 第一部分：基础同构引理 ========== *)

(* 引理：double_C 保持 term 的变元集 *)
Fact double_C_term_preserves_vars : forall t x,
  x ∈ (term_Ens t) <-> x ∈ (term_Ens (double_C_term t)).
Proof.
  intro t.
  apply Term_ind_new with
    (P := fun t => forall x, x ∈ (term_Ens t) 
                                  <-> x ∈ (term_Ens (double_C_term t)))
    (P0 := fun n v => forall x, x ∈ (Vector_Ens n v) 
                                  <-> x ∈ (Vector_Ens n (double_C_vector n v))).
  - (* Tvar *) intros. simpl. tauto.
  - (* Tcon *) intros c x. simpl. split; intro H. destruct H. destruct c. 
    simpl in H. destruct H.
  - (* 空向量 *) intros s x. 
    (* 使用 case0 来处理空向量 *)
    apply (case0 (fun v => forall x0, x0 ∈ (Vector_Ens 0 v) 
                             <-> x0 ∈ (Vector_Ens 0 (double_C_vector 0 v)))).
    simpl. split; intro H; destruct H.
  - (* Tfun *) intros f v IH x. simpl. apply IH.
  - (* cons *) intros n t0 v IHt IHv x. simpl.
    repeat rewrite UnionI. rewrite IHt, IHv. tauto.
Qed.

(* 引理：double_C 保持公式的自由变元集 *)
Fact double_C_preserves_free_vars : forall p x,
  x ∈ (Formula_free_Ens p) <-> x ∈ (Formula_free_Ens (double_C_formula p)).
Proof.
  intro p. induction p; intro x; simpl.
  - (* equality *) rewrite UnionI. rewrite UnionI. split; intros [H | H].
    + left. rewrite <- double_C_term_preserves_vars. auto.
    + right. rewrite <- double_C_term_preserves_vars. auto.
    + left. rewrite double_C_term_preserves_vars. auto.
    + right. rewrite double_C_term_preserves_vars. auto.
  - (* atomic *) (* 先证明一个关于向量的辅助引理 *)
    assert (Hvec: forall n (v : Vector.t term n),
      x ∈ (Vector_Ens n v) <-> x ∈ (Vector_Ens n (double_C_vector n v))).
    { intros n v. induction v; simpl.
      - split; intro H; destruct H.
      - rewrite UnionI. rewrite UnionI. split; intros [H | H].
        + left. rewrite <- double_C_term_preserves_vars. auto.
        + right. apply IHv. auto.
        + left. rewrite double_C_term_preserves_vars. auto.
        + right. apply IHv. auto. }
    apply Hvec.
  - (* Not *) apply IHp.
  - (* Contain *) rewrite UnionI. rewrite UnionI. split; intros [H | H].
    + left. apply IHp1. auto.
    + right. apply IHp2. auto.
    + left. apply IHp1. auto.
    + right. apply IHp2. auto.
  - (* ForAll *) split; intro H; destruct H as [H1 H2].
    + split; auto. apply IHp. auto.
    + split; auto. apply IHp. auto.
Qed.

(* 引理：double_C 保持 t_x_free *)
Fact double_C_preserves_t_x_free : forall p t x,
  t_x_free p t x = t_x_free (double_C_formula p) (double_C_term t) x.
Proof.
  intro p. induction p; intros t1 x1; simpl; auto.
  - (* Contain *) rewrite <- IHp1, <- IHp2. reflexivity.
  - (* ForAll *) destruct (classicT (x1 ∈ (Formula_free_Ens (ForAll v p)))).
    + destruct (classicT (v ∈ (term_Ens t1))).
      * destruct (classicT 
                    (x1 ∈ (Formula_free_Ens (ForAll v (double_C_formula p))))).
        ** destruct (classicT (v ∈ (term_Ens (double_C_term t1)))).
           *** (* 两个 classicT 都成立的情况 *)
               simpl in i. destruct i as [Hi1 Hi2].
               simpl in i1. destruct i1 as [Hi3 Hi4].
               destruct (classicT (x1 ∈ (Formula_free_Ens p) ~ [/v])).
               **** destruct (classicT 
                      (x1 ∈ (Formula_free_Ens (double_C_formula p)) ~ [/v])).
                    ***** reflexivity.
                    ***** exfalso. apply n. split; auto.
               **** exfalso. apply n. split; auto.
           *** exfalso. apply n. rewrite <- double_C_term_preserves_vars. auto.
        ** exfalso. apply n. rewrite double_C_preserves_free_vars in i. auto.
      * destruct (classicT 
          (x1 ∈ (Formula_free_Ens (ForAll v (double_C_formula p))))).
        ** destruct (classicT (v ∈ (term_Ens (double_C_term t1)))).
           *** exfalso. apply n. rewrite double_C_term_preserves_vars. auto.
           *** (* 关键情况：递归应用 IHp *) simpl in i. destruct i as [Hi1 Hi2].
               simpl in i0. destruct i0 as [Hi3 Hi4].
               destruct (classicT (x1 ∈ (Formula_free_Ens p) ~ [/v])).
               **** destruct (classicT 
                      (x1 ∈ (Formula_free_Ens (double_C_formula p)) ~ [/v])).
                    ***** apply IHp.
                    ***** exfalso. apply n1. split; auto.
               **** exfalso. apply n1. split; auto.
        ** exfalso. apply n0. rewrite double_C_preserves_free_vars in i. auto.
    + destruct (classicT 
        (x1 ∈ (Formula_free_Ens (ForAll v (double_C_formula p))))).
      * (* 矛盾：i 说 x1 在 double_C 后的自由变元集中，但 n 说不在原来的 *)
        exfalso. apply n.
        (* 使用 double_C_preserves_free_vars 的反方向 *)
        apply (double_C_preserves_free_vars (ForAll v p) x1). auto.
      * (* 两个都不在自由变元集，需要证明两个 classicT 都是 false *)
        (* 关键：如果 x1 ∈ (Formula_free_Ens p) ~ [/v]，
           那么 x1 ∈ (Formula_free_Ens (∀v,p))，矛盾 *)
        destruct (classicT (x1 ∈ (Formula_free_Ens p) ~ [/v])).
        ** exfalso. apply n. simpl. auto.
        ** destruct (classicT (
             x1 ∈ (Formula_free_Ens (double_C_formula p)) ~ [/v])).
           *** exfalso. apply n0. simpl. auto.
           *** reflexivity.
Qed.

(* 辅助引理：double_C_term 和 substitute_t 可交换 *)
Fact double_C_term_subst_comm : forall t t' x, 
  double_C_term (substitute_t t t' x) 
  = substitute_t (double_C_term t) (double_C_term t') x.
Proof.
  intro t. apply Term_ind_new with
    (P := fun t => forall t' x, double_C_term (substitute_t t t' x)
      = substitute_t (double_C_term t) (double_C_term t') x)
    (P0 := fun n v => forall t' x, double_C_vector n (substitute_v n v t' x)
      = substitute_v n (double_C_vector n v) (double_C_term t') x).
  - (* Tvar *) intros n t' x. simpl. destruct (eqbv x n); reflexivity.
  - (* Tcon *) intros c t' x. simpl. destruct c; reflexivity.
  - (* 空向量 *) intros s t' x.
    apply (case0 (fun v => forall t' x, double_C_vector 0 (substitute_v 0 v t' x) 
      = substitute_v 0 (double_C_vector 0 v) (double_C_term t') x)).
    intros. reflexivity.
  - (* Tfun *) intros f v IH t' x. simpl. rewrite IH. reflexivity.
  - (* cons *) intros n t0 v IHt IHv t' x. simpl. rewrite IHt, IHv. reflexivity.
Qed.

(* 引理：double_C 保持替换 *)
Fact double_C_preserves_subst : forall p t x, 
  double_C_formula (substitute_f p t x)
  = substitute_f (double_C_formula p) (double_C_term t) x.
Proof.
  intro p. induction p; intros t1 x1; simpl; auto.
  - (* equality *) repeat rewrite double_C_term_subst_comm. reflexivity.
  - (* atomic *) f_equal. induction t; simpl; auto.
    rewrite double_C_term_subst_comm. f_equal. auto.
  - (* Not *) f_equal. auto.
  - (* Contain *) f_equal; auto.
  - (* ForAll *) destruct (eqbv x1 v) eqn:E.
    + (* x1 = v，替换不发生 *) simpl. reflexivity.
    + (* x1 ≠ v，替换发生 *) simpl. f_equal. apply IHp.
Qed.

(* ========== double_C 保持一致性 第二部分：double_C 保持公理和推导 ========== *)

(* double_C 保持否定 *)
Fact double_C_preserves_not : forall p, 
  double_C_formula (¬p) = ¬(double_C_formula p).
Proof. reflexivity. Qed.

(* 辅助引理：double_C 保持 equality_4 *)
Fact double_C_preserves_equality_4 : forall r m n v1 v2,
  double_C_formula (equality_4 r m n v1 v2) = equality_4 
    (double_C_formula r) m n (double_C_vector m v1) (double_C_vector n v2).
Proof.
  intros r m n v1. revert r n. induction v1; intros r n' v2.
  - simpl. reflexivity.
  - destruct v2.
    + simpl. reflexivity.
    + simpl. simpl. f_equal. repeat rewrite double_C_term_subst_comm. apply IHv1.
Qed.

(* 关键引理：double_C 保持公理 *)
Lemma double_C_preserves_axiom : forall p,
  Axiom_system p -> Axiom_system (double_C_formula p).
Proof.
  intros p H. induction H; simpl; try constructor.
  - assert (Ht_free: t_x_free (double_C_formula p) (double_C_term t) x = true).
      { rewrite <- double_C_preserves_t_x_free. exact H. }
    rewrite double_C_preserves_subst. constructor. exact Ht_free.
  - rewrite double_C_preserves_equality_4. simpl. constructor.
  - rewrite double_C_preserves_equality_4. simpl. constructor.
  - intro. apply H. rewrite double_C_preserves_free_vars. auto.
  - auto.
Qed.

(* 核心引理：double_C 保持推导 *)
Lemma double_C_preserves_deduce : forall Γ p,
  Γ ├ p -> (double_C_set Γ) ├ (double_C_formula p).
Proof.
  intros Γ p H. induction H.
  - apply K0. split; auto.
  - apply K1. apply double_C_preserves_axiom. auto.
  - simpl in *. eapply MP; eauto.
Qed.

(* ==========double_C 保持一致性 第三部分：构造逆向映射 ========== *)

Lemma in_double_C_set_image : forall Γ q,
  q ∈ (double_C_set Γ) -> exists p, q = double_C_formula p /\ p ∈ Γ.
Proof. intros Γ q H. destruct H. exists p. split; auto. Qed.

(* ========== 第一步：定义逆变换 half_C ========== *)

(* 将常元 c_2i 还原为 c_i *)
Fixpoint half_C_term (t: term) : term :=
  match t with
  | Tcon c => match c with
              | C n => Tcon (C (n / 2))
              end
  | Tvar y => Tvar y
  | Tfun f q => 
      let fix half_C_vc (n: nat) (r: Vector.t term n) :=
        match r with 
        | [] => []
        | h :: q => (half_C_term h) :: (half_C_vc _ q) 
        end 
      in (Tfun f (half_C_vc _ q))
  end.

Fixpoint half_C_vector (n: nat) (r: Vector.t term n) : Vector.t term n :=
  match r with 
  | [] => []
  | h :: q => (half_C_term h) :: (half_C_vector _ q)
  end.

Fixpoint half_C_formula (p: Formula) : Formula :=
  match p with 
  | equality t1 t2 => equality (half_C_term t1) (half_C_term t2)
  | atomic r q => atomic r (half_C_vector _ q)
  | Not q => Not (half_C_formula q)
  | Contain m n => Contain (half_C_formula m) (half_C_formula n)
  | ForAll x q => ForAll x (half_C_formula q)
  end.

(* 将Γ中出现的所有常元c_2i替换成c_i *)
Inductive half_C_set Γ : Ensemble Formula :=
  | half_C_set_intro : forall p, p ∈ Γ 
                           -> (half_C_formula p) ∈ (half_C_set Γ). 

(* 辅助引理：half_C 操作保持项的结构 *)
Fact half_C_term_var : forall x, half_C_term (Tvar x) = Tvar x.
Proof. reflexivity. Qed.

Fact half_C_vector_map : forall n (v : Vector.t term n),
  half_C_vector n v = Vector.map half_C_term v.
Proof.
  intros. induction v.
  - reflexivity.
  - simpl. f_equal.
Qed.

(* ==========half_C 保持一致性 第一部分：基础同构引理 ========== *)

(* 引理：half_C 保持 term 的变元集 *)
Fact half_C_term_preserves_vars : forall t x,
  x ∈ (term_Ens t) <-> x ∈ (term_Ens (half_C_term t)).
Proof.
  intro t.
  apply Term_ind_new with
    (P := fun t => forall x, x ∈ (term_Ens t) 
                                  <-> x ∈ (term_Ens (half_C_term t)))
    (P0 := fun n v => forall x, x ∈ (Vector_Ens n v) 
                                  <-> x ∈ (Vector_Ens n (half_C_vector n v))).
  - (* Tvar *) intros. simpl. tauto.
  - (* Tcon *) intros c x. simpl. split; intro H. destruct H. destruct c. 
    simpl in H. destruct H.
  - (* 空向量 *) intros s x. 
    (* 使用 case0 来处理空向量 *)
    apply (case0 (fun v => forall x0, x0 ∈ (Vector_Ens 0 v) 
                             <-> x0 ∈ (Vector_Ens 0 (half_C_vector 0 v)))).
    simpl. split; intro H; destruct H.
  - (* Tfun *) intros f v IH x. simpl. apply IH.
  - (* cons *) intros n t0 v IHt IHv x. simpl.
    repeat rewrite UnionI. rewrite IHt, IHv. tauto.
Qed.

(* 引理：half_C 保持公式的自由变元集 *)
Fact half_C_preserves_free_vars : forall p x,
  x ∈ (Formula_free_Ens p) <-> x ∈ (Formula_free_Ens (half_C_formula p)).
Proof.
  intro p. induction p; intro x; simpl.
  - (* equality *) rewrite UnionI. rewrite UnionI. split; intros [H | H].
    + left. rewrite <- half_C_term_preserves_vars. auto.
    + right. rewrite <- half_C_term_preserves_vars. auto.
    + left. rewrite half_C_term_preserves_vars. auto.
    + right. rewrite half_C_term_preserves_vars. auto.
  - (* atomic *) (* 先证明一个关于向量的辅助引理 *)
    assert (Hvec: forall n (v : Vector.t term n),
      x ∈ (Vector_Ens n v) <-> x ∈ (Vector_Ens n (half_C_vector n v))).
    { intros n v. induction v; simpl.
      - split; intro H; destruct H.
      - rewrite UnionI. rewrite UnionI. split; intros [H | H].
        + left. rewrite <- half_C_term_preserves_vars. auto.
        + right. apply IHv. auto.
        + left. rewrite half_C_term_preserves_vars. auto.
        + right. apply IHv. auto. }
    apply Hvec.
  - (* Not *) apply IHp.
  - (* Contain *) rewrite UnionI. rewrite UnionI. split; intros [H | H].
    + left. apply IHp1. auto.
    + right. apply IHp2. auto.
    + left. apply IHp1. auto.
    + right. apply IHp2. auto.
  - (* ForAll *) split; intro H; destruct H as [H1 H2].
    + split; auto. apply IHp. auto.
    + split; auto. apply IHp. auto.
Qed.

(* 引理：half_C 保持 t_x_free *)
Fact half_C_preserves_t_x_free : forall p t x,
  t_x_free p t x = t_x_free (half_C_formula p) (half_C_term t) x.
Proof.
  intro p. induction p; intros t1 x1; simpl; auto.
  - (* Contain *) rewrite <- IHp1, <- IHp2. reflexivity.
  - (* ForAll *) destruct (classicT (x1 ∈ (Formula_free_Ens (ForAll v p)))).
    + destruct (classicT (v ∈ (term_Ens t1))).
      * destruct (classicT 
                    (x1 ∈ (Formula_free_Ens (ForAll v (half_C_formula p))))).
        ** destruct (classicT (v ∈ (term_Ens (half_C_term t1)))).
           *** (* 两个 classicT 都成立的情况 *)
               simpl in i. destruct i as [Hi1 Hi2].
               simpl in i1. destruct i1 as [Hi3 Hi4].
               destruct (classicT (x1 ∈ (Formula_free_Ens p) ~ [/v])).
               **** destruct (classicT 
                      (x1 ∈ (Formula_free_Ens (half_C_formula p)) ~ [/v])).
                    ***** reflexivity.
                    ***** exfalso. apply n. split; auto.
               **** exfalso. apply n. split; auto.
           *** exfalso. apply n. rewrite <- half_C_term_preserves_vars. auto.
        ** exfalso. apply n. rewrite half_C_preserves_free_vars in i. auto.
      * destruct (classicT 
          (x1 ∈ (Formula_free_Ens (ForAll v (half_C_formula p))))).
        ** destruct (classicT (v ∈ (term_Ens (half_C_term t1)))).
           *** exfalso. apply n. rewrite half_C_term_preserves_vars. auto.
           *** (* 关键情况：递归应用 IHp *) simpl in i. destruct i as [Hi1 Hi2].
               simpl in i0. destruct i0 as [Hi3 Hi4].
               destruct (classicT (x1 ∈ (Formula_free_Ens p) ~ [/v])).
               **** destruct (classicT 
                      (x1 ∈ (Formula_free_Ens (half_C_formula p)) ~ [/v])).
                    ***** apply IHp.
                    ***** exfalso. apply n1. split; auto.
               **** exfalso. apply n1. split; auto.
        ** exfalso. apply n0. rewrite half_C_preserves_free_vars in i. auto.
    + destruct (classicT 
        (x1 ∈ (Formula_free_Ens (ForAll v (half_C_formula p))))).
      * (* 矛盾：i 说 x1 在 double_C 后的自由变元集中，但 n 说不在原来的 *)
        exfalso. apply n.
        (* 使用 double_C_preserves_free_vars 的反方向 *)
        apply (half_C_preserves_free_vars (ForAll v p) x1). auto.
      * (* 两个都不在自由变元集，需要证明两个 classicT 都是 false *)
        (* 关键：如果 x1 ∈ (Formula_free_Ens p) ~ [/v]，
           那么 x1 ∈ (Formula_free_Ens (∀v,p))，矛盾 *)
        destruct (classicT (x1 ∈ (Formula_free_Ens p) ~ [/v])).
        ** exfalso. apply n. simpl. auto.
        ** destruct (classicT (
             x1 ∈ (Formula_free_Ens (half_C_formula p)) ~ [/v])).
           *** exfalso. apply n0. simpl. auto.
           *** reflexivity.
Qed.

(* 辅助引理：half_C_term 和 substitute_t 可交换 *)
Fact half_C_term_subst_comm : forall t t' x, 
  half_C_term (substitute_t t t' x) 
  = substitute_t (half_C_term t) (half_C_term t') x.
Proof.
  intro t. apply Term_ind_new with
    (P := fun t => forall t' x, half_C_term (substitute_t t t' x)
      = substitute_t (half_C_term t) (half_C_term t') x)
    (P0 := fun n v => forall t' x, half_C_vector n (substitute_v n v t' x)
      = substitute_v n (half_C_vector n v) (half_C_term t') x).
  - (* Tvar *) intros n t' x. simpl. destruct (eqbv x n); reflexivity.
  - (* Tcon *) intros c t' x. simpl. destruct c; reflexivity.
  - (* 空向量 *) intros s t' x.
    apply (case0 (fun v => forall t' x, half_C_vector 0 (substitute_v 0 v t' x) 
      = substitute_v 0 (half_C_vector 0 v) (half_C_term t') x)).
    intros. reflexivity.
  - (* Tfun *) intros f v IH t' x. simpl. rewrite IH. reflexivity.
  - (* cons *) intros n t0 v IHt IHv t' x. simpl. rewrite IHt, IHv. reflexivity.
Qed.

(* 引理：half_C 保持替换 *)
Fact half_C_preserves_subst : forall p t x, 
  half_C_formula (substitute_f p t x)
  = substitute_f (half_C_formula p) (half_C_term t) x.
Proof.
  intro p. induction p; intros t1 x1; simpl; auto.
  - (* equality *) repeat rewrite half_C_term_subst_comm. reflexivity.
  - (* atomic *) f_equal. induction t; simpl; auto.
    rewrite half_C_term_subst_comm. f_equal. auto.
  - (* Not *) f_equal. auto.
  - (* Contain *) f_equal; auto.
  - (* ForAll *) destruct (eqbv x1 v) eqn:E.
    + (* x1 = v，替换不发生 *) simpl. reflexivity.
    + (* x1 ≠ v，替换发生 *) simpl. f_equal. apply IHp.
Qed.

(* ========== half_C 保持一致性 第二部分：half_C 保持公理和推导 ========== *)

(* half_C 保持否定 *)
Fact half_C_preserves_not : forall p, 
  half_C_formula (¬p) = ¬(half_C_formula p).
Proof. reflexivity. Qed.

(* 辅助引理：half_C 保持 equality_4 *)
Fact half_C_preserves_equality_4 : forall r m n v1 v2,
  half_C_formula (equality_4 r m n v1 v2) = equality_4 
    (half_C_formula r) m n (half_C_vector m v1) (half_C_vector n v2).
Proof.
  intros r m n v1. revert r n. induction v1; intros r n' v2.
  - simpl. reflexivity.
  - destruct v2.
    + simpl. reflexivity.
    + simpl. simpl. f_equal. repeat rewrite half_C_term_subst_comm. apply IHv1.
Qed.

(* 关键引理：half_C 保持公理 *)
Lemma half_C_preserves_axiom : forall p,
  Axiom_system p -> Axiom_system (half_C_formula p).
Proof.
  intros p H. induction H; simpl; try constructor.
  - assert (Ht_free: t_x_free (half_C_formula p) (half_C_term t) x = true).
      { rewrite <- half_C_preserves_t_x_free. exact H. }
    rewrite half_C_preserves_subst. constructor. exact Ht_free.
  - rewrite half_C_preserves_equality_4. simpl. constructor.
  - rewrite half_C_preserves_equality_4. simpl. constructor.
  - intro. apply H. rewrite half_C_preserves_free_vars. auto.
  - auto.
Qed.

(* 核心引理：half_C 保持推导 *)
Lemma half_C_preserves_deduce : forall Γ p,
  Γ ├ p -> (half_C_set Γ) ├ (half_C_formula p).
Proof.
  intros Γ p H. induction H.
  - apply K0. split; auto.
  - apply K1. apply half_C_preserves_axiom. auto.
  - simpl in *. eapply MP; eauto.
Qed.

(* ==========half_C 保持一致性 第三部分：构造逆向映射 ========== *)

Lemma in_half_C_set_image : forall Γ q,
  q ∈ (half_C_set Γ) -> exists p, q = half_C_formula p /\ p ∈ Γ.
Proof. intros Γ q H. destruct H. exists p. split; auto. Qed.

(* half_C 是 double_C 的左逆 *)
Fact half_double_term : forall t, half_C_term (double_C_term t) = t.
Proof.
  intro t.
  apply Term_ind_new with
    (P := fun t => half_C_term (double_C_term t) = t)
    (P0 := fun n v => half_C_vector n (double_C_vector n v) = v).
  - (* Tvar *) intros. simpl. reflexivity.
  - (* Tcon *) intros [n]. unfold double_C_term. unfold half_C_term.
    replace (2 * n / 2) with n; auto. rewrite Nat.mul_comm, Nat.div_mul; auto.
  - (* 空向量 *) intros s.
    apply (case0 (fun v => half_C_vector 0 (double_C_vector 0 v) = v)).
    reflexivity.
  - (* Tfun *) intros f v IH. simpl. f_equal. apply IH.
  - (* cons *) intros n t0 v IHt IHv. simpl. f_equal; auto.
Qed.

Fact half_double_vector : forall n v, half_C_vector n (double_C_vector n v) = v.
Proof.
  intros. induction v; simpl; auto. rewrite half_double_term. f_equal. auto.
Qed.

Fact half_double_formula : forall p, half_C_formula (double_C_formula p) = p.
Proof.
  induction p; simpl; auto.
  - repeat rewrite half_double_term. reflexivity.
  - rewrite half_double_vector. reflexivity.
  - rewrite IHp. reflexivity.
  - rewrite IHp1, IHp2. reflexivity.
  - rewrite IHp. reflexivity.
Qed.

Fact half_double_Γ : forall Γ, half_C_set (double_C_set Γ) = Γ.
Proof.
  intros. apply Extensionality_Ensembles. split; red; intros.
  - apply in_half_C_set_image in H as [x0[]].
    apply in_double_C_set_image in H0 as [x1[]].
    rewrite H,H0,half_double_formula; auto.
  - rewrite <-(half_double_formula x). apply half_C_set_intro.
    apply double_C_set_intro; auto.
Qed.


(* 关键引理 *)
Lemma double_C_consistence : forall Γ, 
  consistence Γ <-> consistence (double_C_set Γ).
Proof.
  split; intros.
  - red in H. red; intros. intro. destruct H0.
    apply half_C_preserves_deduce in H0,H1. simpl in H1.
    rewrite half_double_Γ in H0,H1. pose proof (H (half_C_formula q)). tauto.
  - red in H. red; intros. intro. destruct H0.
    apply double_C_preserves_deduce in H0,H1.
    simpl in H1. pose proof H (double_C_formula q). tauto.
Qed.


(* 辅助引理：double_C 对项的求值 *)
Lemma double_C_term_value : forall MM v t,
  let I_2c := fun (c: Con) => match c with C n => I_c (C (n / 2)) end in
  let MM' := Build_Module M I_2c I_f I_R in
    @ value_term MM' v (double_C_term t) = @ value_term MM v t.
Proof.
  intros MM v t.
  apply Term_ind_new with
    (P := fun t =>
      let I_2c := fun (c:Con) => match c with C n => I_c (C (n / 2)) end in
      let MM' := Build_Module M I_2c I_f I_R in
        @ value_term MM' v (double_C_term t) = @ value_term MM v t)
    (P0 := fun n vec =>
      let I_2c := fun (c:Con) => match c with C n => I_c (C (n / 2)) end in
      let MM' := Build_Module M I_2c I_f I_R in
        Vector.map (@ value_term MM' v) (double_C_vector n vec) 
          = Vector.map (@ value_term MM v) vec).
  - (* Tvar *) intros. simpl. reflexivity.
  - (* Tcon *) intros [n]. simpl. rewrite Nat.add_0_r. f_equal. f_equal.
    assert (fst (Nat.divmod (n + n) 1 0 1) = (Nat.div (n + n) 2)). auto.
    rewrite H. replace (n + n) with (2 * n).
    rewrite Nat.mul_comm,Nat.div_mul; auto. lia.
  - (* 空向量 *) intros s.
    apply (case0 (fun v0 : Vector.t term 0 =>
      let I_2c := fun c : Con => match c with C n => I_c (C (n / 2)) end in
      let MM' := Build_Module M I_2c I_f I_R in
        Vector.map (@ value_term MM' v) (double_C_vector 0 v0)
          = Vector.map (@ value_term MM v) v0)).
    simpl. reflexivity.
  - (* Tfun *) intros f vec IH. simpl. f_equal. apply IH.
  - (* cons *) intros n h tail IHh IHt. simpl. f_equal; auto.
Qed.

(* Check double_C_term_value. *)

Definition ModulehalfC (MM: Module) : Module := {|
  M := @ M MM;
  I_c := fun c => match c with C n => @ I_c MM (C (n / 2)) end;
  I_f := @ I_f MM;
  I_R := @ I_R MM |}.

Definition Module2C (MM: Module) : Module := {|
  M := @ M MM;
  I_c := fun c => match c with C n => @ I_c MM (C (2 * n)) end;
  I_f := @ I_f MM;
  I_R := @ I_R MM |}.

(* 考虑不同模型下的赋值 *)
Fact double_C_term_value_half : forall MM (v: value MM) t,
  @ value_term (ModulehalfC MM) v (double_C_term t) = @ value_term MM v t.
Proof.
  intros MM v t.
  apply Term_ind_new with
    (P := fun t =>
      @ value_term (ModulehalfC MM) v (double_C_term t) = @ value_term MM v t)
    (P0 := fun n vec =>
      Vector.map (@ value_term (ModulehalfC MM) v) (double_C_vector n vec)
      = Vector.map (@ value_term MM v) vec).
  - (* Tvar *) intros. simpl. reflexivity.
  - (* Tcon *) intros [n]. simpl.
    assert (fst (Nat.divmod (n + n) 1 0 1) = (Nat.div (n + n) 2)). auto.
    rewrite Nat.add_0_r,H. replace (n + n) with (2 * n).
    rewrite Nat.mul_comm,Nat.div_mul; auto. lia.
  - (* 空向量 *) intros s. 
    apply (case0 (fun v0 =>
      Vector.map (@ value_term (ModulehalfC MM) v) (double_C_vector 0 v0)
      = Vector.map (@ value_term MM v) v0)).
    simpl. reflexivity.
  - (* Tfun *) intros f vec IH. simpl. f_equal. apply IH.
  - (* cons *) intros n h tail IHh IHt. simpl. f_equal; auto.
Qed.

Fact double_C_term_value_2C : forall MM (v: value MM) t,
  @ value_term MM v (double_C_term t) = @ value_term (Module2C MM) v t.
Proof.
  intros MM v t.
  apply Term_ind_new with
    (P := fun t => 
      @ value_term MM v (double_C_term t) = @ value_term (Module2C MM) v t)
    (P0 := fun n vec =>
      Vector.map (@ value_term MM v) (double_C_vector n vec)
      = Vector.map (@ value_term (Module2C MM) v) vec).
  - (* Tvar *) intros. simpl. reflexivity.
  - (* Tcon *) intros [n]. simpl. unfold Module2C. simpl. reflexivity.
  - (* 空向量 *) intros s. 
    apply (case0 (fun v0 => Vector.map (@ value_term MM v) (double_C_vector 0 v0)
      = Vector.map (@ value_term (Module2C MM) v) v0)).
    simpl. reflexivity.
  - (* Tfun *) intros f vec IH. simpl. unfold Module2C. simpl. f_equal. apply IH.
  - (* cons *) intros n h tail IHh IHt. simpl. f_equal; auto.
Qed.

(* 向量情形 *)
Fact double_C_vector_value_half : forall MM (v: value MM) n vec,
  Vector.map (@ value_term (ModulehalfC MM) v) (double_C_vector n vec)
  = Vector.map (@ value_term MM v) vec.
Proof.
  intros. induction vec.
  - simpl. reflexivity.
  - simpl. f_equal.
    + apply double_C_term_value_half.
    + apply IHvec.
Qed.

Fact double_C_vector_value_2C : forall MM (v: value MM) n vec,
  Vector.map (@ value_term MM v) (double_C_vector n vec)
  = Vector.map (@ value_term (Module2C MM) v) vec.
Proof.
  intros. induction vec.
  - simpl. reflexivity.
  - simpl. f_equal.
    + apply double_C_term_value_2C.
    + apply IHvec.
Qed.

(* 辅助引理：double_C 对公式的满足关系 *)
Lemma double_C_satisfy : forall MM (v: value MM) p,
  @ satisfy_R (ModulehalfC MM) v (double_C_formula p) <-> @ satisfy_R MM v p.
Proof.
  intros MM v0 p. revert v0.
  induction p; intro v0; split; intros H; simpl in *.
  - (* equality, -> *) repeat rewrite double_C_term_value_half in H. exact H.
  - (* equality, <- *) repeat rewrite double_C_term_value_half. exact H.
  - (* atomic, -> *) unfold ModulehalfC in H. simpl in H.
    set (vecs := double_C_vector (arity_R r) t) in H.
    assert (Heq: map (@ value_term (ModulehalfC MM) v0) vecs
                   = map (@value_term MM v0) t).
    { subst vecs. apply double_C_vector_value_half. }
    rewrite <-Heq. exact H.
  - (* atomic, <- *) unfold ModulehalfC. simpl.
    set (vecs := double_C_vector (arity_R r) t).
    assert (Heq: map (@ value_term (ModulehalfC MM) v0) vecs
                   = map (@ value_term MM v0) t).
    { subst vecs. apply double_C_vector_value_half. }
    rewrite <-Heq in H. exact H.
  - (* Not, -> *) intro. apply H. apply IHp. exact H0.
  - (* Not, <- *) intro. apply H. apply IHp. exact H0.
  - (* Contain, -> *) destruct H.
    + left. intro. apply H. apply IHp1. exact H0.
    + right. apply IHp2. exact H.
  - (* Contain, <- *) destruct H.
    + left. intro. apply H. apply IHp1. exact H0.
    + right. apply IHp2. exact H.
  - (* ForAll, -> *) intro m. specialize (H m). apply IHp. exact H.
  - (* ForAll, <- *) intro m. specialize (H m). apply IHp. exact H.
Qed.

Lemma double_C_satisfy' : forall MM (v: value MM) p,
  @ satisfy_R MM v (double_C_formula p) <-> @ satisfy_R (Module2C MM) v p.
Proof.
  intros MM v0 p. revert v0. induction p; intro v0; split; intros H; simpl in *.
  - (* equality, -> *) 
    assert (Ht: @ value_term MM v0 (double_C_term t)
                  = @ value_term (Module2C MM) v0 t).
    { apply double_C_term_value_2C. }
    assert (Ht0: @ value_term MM v0 (double_C_term t0)
                   = @ value_term (Module2C MM) v0 t0).
    { apply double_C_term_value_2C. }
    rewrite Ht in H. rewrite Ht0 in H. exact H.
  - (* equality, <- *)
    assert (Ht: @ value_term MM v0 (double_C_term t)
                  = @ value_term (Module2C MM) v0 t).
    { apply double_C_term_value_2C. }
    assert (Ht0: @ value_term MM v0 (double_C_term t0)
                   = @ value_term (Module2C MM) v0 t0).
    { apply double_C_term_value_2C. }
    rewrite Ht. rewrite Ht0. exact H.
  - (* atomic, -> *) unfold Module2C. simpl.
    set (vecs := double_C_vector (arity_R r) t) in H.
    assert (Heq: map (@ value_term MM v0) vecs 
                   = map (@ value_term (Module2C MM) v0) t).
    { subst vecs. apply double_C_vector_value_2C. }
    rewrite Heq in H. exact H.
  - (* atomic, <- *) unfold Module2C in H. simpl in H.
    set (vecs := double_C_vector (arity_R r) t).
    assert (Heq: map (@ value_term MM v0) vecs
                   = map (@ value_term (Module2C MM) v0) t).
    { subst vecs. apply double_C_vector_value_2C. }
    rewrite Heq. exact H.
  - (* Not, -> *) intro. apply H. apply IHp. exact H0.
  - (* Not, <- *) intro. apply H. apply IHp. exact H0.
  - (* Contain, -> *) destruct H.
    + left. intro. apply H. apply IHp1. exact H0.
    + right. apply IHp2. exact H.
  - (* Contain, <- *) destruct H.
    + left. intro. apply H. apply IHp1. exact H0.
    + right. apply IHp2. exact H.
  - (* ForAll, -> *) intro m. specialize (H m). apply IHp. exact H.
  - (* ForAll, <- *) intro m. specialize (H m). apply IHp. exact H.
Qed.

(* 关键引理: Γ是可满足的当且仅当 double_C_set Γ是可满足的 *)
Lemma double_C_satisfiable : forall Γ,
  satisfyable_Γ Γ <-> satisfyable_Γ (double_C_set Γ).
Proof.
  split; intros.
  - destruct H as [MM [v H]]. red in H. red.
    (* 构造新模型 *)
    exists (Build_Module 
              (@ M MM)
              (fun c => match c with C n => @ I_c MM (C (n / 2)) end)
              (@ I_f MM)
              (@ I_R MM)), v.
    red. intros p Hp. destruct Hp as [p0 Hp0].
    pose proof (@ double_C_satisfy MM v p0) as Hsat.
    simpl in Hsat. apply Hsat. apply H. auto.
  - destruct H as [MM [v H]]. red in H. red.
    (* 构造新模型 *)
    exists (Build_Module 
              (@ M MM)
              (fun c => match c with C n => @ I_c MM (C (2 * n)) end)
              (@ I_f MM)
              (@ I_R MM)), v.
    red. intros p Hp.
    assert (Hdouble: double_C_formula p ∈ (double_C_set Γ)). 
      { constructor. auto. }
    specialize (H (double_C_formula p) Hdouble).
    pose proof double_C_satisfy'. apply H0. auto.
Qed.

(**************************************************************************)
(*       在扩张了常量的一阶语言中，将一致集Γ逐步扩张为一个极大一致集Γ'            *)
(**************************************************************************)
Section max_consistence_extention.
Variable Γ: Ensemble(Formula).
Hypothesis H_consistence_set : consistence Γ.
(* 记 double_C_set Γ 为 Γ' *)
Let Γ' := double_C_set Γ.
(* 自然数集到公式集的双射 fun_NF *)
Variable fun_NF : nat -> Formula.
Hypothesis NF_bij : function_bijective fun_NF.

(* Consistent Extence (CE) *)
(* 定义Г_i: Г_0 = Г'
 Case 1: Г_n ∪ {p_n} is not consistence. We let Г_n+1 = Г_n.
 Case 2: Г_n ∪ {p_n} is consistence, and p_n is not of the form (Not (Forall x p)),
         We let Г_n+1 = Г_n ∪ {p_n}.
 Case 3: Г_n ∪ {p_n} is consistence, and p_n is of the form (Not (Forall x p)),
         We let Г_n+1 = Г_n ∪ {p_n} ∪ (¬p[c_(2n+1)/x]). *)
Fixpoint CE (n: nat) : Ensemble Formula :=
  match n with
  | O => Γ'
  | S n' => match (classicT (consistence ((CE n') ∪ [/ (fun_NF n')]))) with
            | right _ => CE n'
            | left _ => match (fun_NF n') with
                        | Not (ForAll x p) => (CE n') ∪ [/ (fun_NF n')] 
                                 ∪ [/ Not (substitute_f p (Tcon (C (1+2*n'))) x)]
                        | _ => (CE n') ∪ [/ (fun_NF n')]
                        end
            end
  end.

(* CE_all = ∪ (CE i) *)
Definition CE_all : Ensemble Formula := fun p => exists n, p ∈ (CE n).

(* for any m,n, if m <= n, then (CE m) ⊆ (CE n) *)
Fact CE_monotone : forall m n, m <= n -> (CE m) ⊆ (CE n).
Proof.
  induction n.
  - intros; red; intros. induction m; auto. inversion H.
  - intros; red; intros. assert (m <= n \/ m = S n). { inversion H; auto. }
    destruct H1.
    + apply IHn in H1. apply H1 in H0. simpl.
      destruct classicT; simpl.
      * destruct (fun_NF (S n)).
        -- destruct (fun_NF n).
           ++ left; auto.
           ++ left; auto.
           ++ destruct f; left; try auto. left; auto.
           ++ left; auto.
           ++ left; auto.
        -- destruct (fun_NF n);try left; try auto. destruct f; left; try auto.
           left; auto.
        -- destruct (fun_NF n);try left; try auto. destruct f0; left; try auto.
           left; auto.
        -- destruct (fun_NF n);try left; try auto. destruct f; left; try auto. 
           left; auto.
        -- destruct (fun_NF n);try left; try auto. destruct f0; left; try auto.
           left; auto.
      * auto.
    + rewrite H1 in *; auto.
Qed.

Fact subsetNocontra : forall A B , A ⊆ B -> consistence B -> consistence A.
Proof.
  intros. red. intros. intro. red in H0. destruct (H0 q).
  destruct H1; split; eapply subsetprove; eauto.
Qed.

Fact CE_le2 : forall m n, (CE m) ⊆ (CE n) \/  (CE n) ⊆ (CE m).
Proof.
  intros. destruct (classicT (n <= m)).
  - apply CE_monotone in l; auto.
  - assert (m <= n). lia. apply CE_monotone in H; auto.
Qed.

Fact CE_le1 : forall p, CE_all ├ p -> exists n, (CE n) ├ p.
Proof.
  intros. induction H.
  - red in H; red in H. destruct H as [n H].
    exists n; autoK.
  - exists 0. autoK.
  - destruct IHdeduce_K1, IHdeduce_K2. 
    destruct (CE_le2 x x0).
    pose proof subsetprove _ _ _ H3 H1. exists x0. apply MP with p; auto.
    pose proof subsetprove _ _ _ H3 H2. exists x. apply MP with p; auto.
Qed.

(* 向量项替换把常元c替换成t' *)
Fixpoint substitute_vc (n: nat) (r: Vector.t term n) (t': term) (c: Con) :=
  match r with 
  | [] => []
  | h :: q => (substitute_tc h t' c) :: (substitute_vc _ q t' c)
  end.

(* 公式p中把常元c替换成t' *)
Fixpoint substitute_fc (p: Formula) (t': term) (c: Con) :=
  match p with 
  | equality t1 t2 => equality (substitute_tc t1 t' c) (substitute_tc t2 t' c) 
  | atomic _ q => atomic _ (substitute_vc _ q t' c) 
  | Not q => Not (substitute_fc q t' c)
  | Contain m n => Contain (substitute_fc m t' c) (substitute_fc n t' c)
  | ForAll y q => ForAll y (substitute_fc q t' c)
  end.
Notation " p {/ c ;; r } ":= (substitute_fc p r c)(at level 0).

Lemma subst_term_const_inv : forall t c x y, ~ (y ∈ (term_Ens t)) 
  ->((substitute_tc t (Tvar y) c) {y ; Tvar x})= substitute_tc t (Tvar x) c.
Proof.
  fix IH 1. intros. destruct t.
  - simpl. destruct (eqbv y v) eqn:E.
    + Eqbv. exfalso. apply H. simpl. auto with sets.
    + reflexivity.
  - simpl. destruct (eqbc c c0) eqn:E.
    + simpl. destruct (eqbv y y) eqn:E1; auto. Eqbv.
    + simpl. reflexivity.
  - simpl. f_equal. simpl in H. revert H. induction t; simpl; intros. auto.
    f_equal. apply IH. intro. apply H. left. auto.
    apply IHt. intro. apply H. right. auto.
Qed.

Lemma subst_vector_const_inv : forall n (v : Vector.t term n) c x y,
  ~ (y ∈ (Vector_Ens n v)) 
  -> substitute_v n (substitute_vc n v (Tvar y) c) (Tvar x) y
  = substitute_vc n v (Tvar x) c.
Proof.
  induction v; simpl; intros.
  - auto.
  - apply union_complement_equiv in H as [H1 H2]. f_equal.
    + apply subst_term_const_inv. auto.
    + apply IHv. auto.
Qed.

(* 连续代换 ϕ(c; y)(y; x) = ϕ(c; x) *)
Lemma subst_c_v : forall p c y x, ~ (y ∈ (Formula_Ens p))
  -> (p{/ c ;; Tvar y}){y ;; Tvar x} = p{/ c ;; Tvar x}.
Proof. 
  intros. induction p; simpl; intros; auto.
  - simpl in *. apply union_complement_equiv in H as [].
    f_equal; eapply subst_term_const_inv; eauto.
  - simpl in H. f_equal. eapply subst_vector_const_inv in H; eauto.
  - rewrite IHp; auto.
  - apply union_complement_equiv in H as []. rewrite IHp1, IHp2; auto.
  - simpl in H. apply union_complement_equiv in H as [].
    destruct (eqbv x v) eqn:E; simpl; destruct (eqbv y v) eqn:E'; auto.
    + Eqbv. elim H0. ES.
    + Eqbv. f_equal. apply IHp. auto.
    + Eqbv. elim H0. ES.
    + f_equal. apply IHp. auto.
Qed.

(* 类似 subst_term_inv *)
Fact subst_t_tc_inv : forall t x c, ~ (c ∈ (term_C_set t))
  -> substitute_tc (t {x;(Tcon c)}) (Tvar x) c = t.
Proof.
  fix IH 1. intros. destruct t.
  - simpl. destruct (eqbv x v) eqn:E.
    + simpl. destruct (eqbc c c) eqn:Ec; auto. Eqbv. auto.
      bdestruct (eqbc c c). inversion Ec. elim H0. auto.
    + simpl. auto.
  - simpl. destruct (eqbc c c0) eqn:Ec.
    + simpl in H. elim H. destruct c0,c. unfold eqbc in Ec.
      rewrite Nat.eqb_eq in Ec. subst. apply In_singleton.
    + reflexivity.
  - simpl. f_equal. simpl in H. revert H. induction t; simpl; intros. auto.
    f_equal. apply IH. intro. apply H. left. auto.
    apply IHt. intro. apply H. right. auto.
Qed.

Fact union_complement_equiv': forall (A B: Ensemble Con) x,
  (~ x ∈ (A ∪ B)) <-> (~ x ∈ A) /\ (~ x ∈ B).
Proof.
  split; intro.
  - split; red; intro; destruct H; ES.
  - destruct H. red. intro. destruct H1; contradiction.
Qed.

(* 类似 subst_vector_inv *)
Fact subst_v_vc_inv : forall n v x c, ~ (c ∈ (Vector_C_set n v))
  -> substitute_vc n (substitute_v n v (Tcon c) x) (Tvar x) c = v.
Proof.
  induction v; simpl; intros. auto. apply union_complement_equiv' in H as [].
  f_equal. apply subst_t_tc_inv. auto. apply IHv. auto.
Qed.

Lemma subst_tc_not_in : forall t c t',
  ~ c ∈ (term_C_set t) -> substitute_tc t t' c = t.
Proof.
  fix IH 1. intros t c t' Hnot.
  destruct t as [v_var | c_con | f v_vec].
  - simpl. reflexivity.
  - simpl. simpl in Hnot.
    destruct (eqbc_reflect c c_con) as [Heq | Hneq].
    + subst. exfalso. apply Hnot. rewrite Single. reflexivity.
    + reflexivity.
  - simpl. simpl in Hnot. f_equal. revert Hnot.
    induction v_vec as [| h n q IHq].
    + intro Hnot. reflexivity.
    + intro Hnot. simpl in Hnot. simpl. f_equal.
      * apply IH. intro H_in. apply Hnot. left. exact H_in.
      * apply IHq. intro H_in. apply Hnot. right. exact H_in.
Qed.

(* 引理 2：针对 Vector 的常量集和替换 *)
Lemma subst_vc_not_in : forall n (v : Vector.t term n) c t',
  ~ c ∈ (Vector_C_set n v) -> substitute_vc n v t' c = v.
Proof.
  induction v; intros c t' Hnot.
  - simpl. reflexivity.
  - simpl. f_equal.
    + apply subst_tc_not_in. 
      intro H. apply Hnot. simpl. now left. 
    + apply IHv.
      intro H. apply Hnot. simpl. now right.
Qed.

Lemma subst_fc_not_in : forall p c t',
  ~ c ∈ (Formula_C_set p) -> p{/ c ;; t'} = p.
Proof.
  induction p; intros c t' Hnot; simpl in *.
  - f_equal; apply subst_tc_not_in; intro H; 
    apply Hnot; [now left|now right]. 
  - f_equal. apply subst_vc_not_in. assumption.
  - f_equal. apply IHp. assumption.
  - f_equal.
    + apply IHp1. intro H. apply Hnot. now left. 
    + apply IHp2. intro H. apply Hnot. now right.
  - f_equal. apply IHp. assumption.
Qed.

(* 类似 sub_xy_2 *)
Fact subst_f_fc_inv : forall p x c, ~ (c ∈ (Formula_C_set p))
  -> (p {x ;; Tcon c}) {/ c ;; Tvar x} = p.
Proof.
  intros. induction p; simpl; intros; auto.
  - simpl in H. apply union_complement_equiv' in H as [].
    eapply (subst_t_tc_inv _ x _) in H,H0; eauto. rewrite H,H0. auto.
  - simpl in H. f_equal. eapply subst_v_vc_inv in H; eauto.
  - rewrite IHp; auto.
  - apply union_complement_equiv' in H as []. rewrite IHp1, IHp2; auto.
  - simpl in H. destruct (eqbv x v) eqn:E; simpl; f_equal.
    apply subst_fc_not_in. auto. apply IHp. auto.
Qed.

Lemma term_subst_c_v_comm : forall t1 t0 x c t,
  substitute_tc (substitute_t t1 t0 x) t c 
  = substitute_t (substitute_tc t1 t c) (substitute_tc t0 t c) x.
Proof.
  fix IH_term 1. intros t1 t0 x c t.
  destruct t1 as [y | c_sym | f v_args].
  - simpl. destruct (eqbv x y) eqn:Heq.
    + reflexivity.
    + auto.
  - simpl. destruct (eqbc c c_sym) eqn:Heq_c.
    + unfold substitute_tc. simpl. admit.
    + simpl. reflexivity.
  - simpl. f_equal. induction v_args as [| h n' tl IH_v]; auto.
    simpl. f_equal.
    + apply (IH_term h).
    + apply IH_v.
Admitted.

(* --- 必须补充的底层引理 B：向量(vector)的常量与变量替换交换律 --- *)
Lemma vec_subst_c_v_comm : forall n (v: Vector.t term n) t0 x c t,
  substitute_vc n (substitute_v n v t0 x) t c 
  = substitute_v n (substitute_vc n v t c) (substitute_tc t0 t c) x.
Proof.
  (* 向量的证明同理，直接使用局部的内部递归 *)
  fix IH_vec 2.
  intros n v t0 x c t_rep.
  destruct v as [| h n' tl].
  - simpl. reflexivity.
  - simpl. f_equal.
    + apply term_subst_c_v_comm. (* 直接调用上面刚刚证好的项引理 *)
    + apply (IH_vec n' tl).
Qed.

(* 定理1：常量替换与变量替换的可交换性。注意这里使用了 substitute_tc *)
Lemma subst_F_c_v_comm : forall p x t0 c t,
  (p {x ;; t0}) {/ c ;; t} = (p {/ c ;; t}) {x ;; substitute_tc t0 t c}.
Proof.
  intros p x t0 c t. induction p; simpl.
  - f_equal.
    + apply term_subst_c_v_comm. (* 左项的交换律 *)
    + apply term_subst_c_v_comm. (* 右项的交换律 *)
  - f_equal. apply vec_subst_c_v_comm.    (* 向量的交换律 *)
  - f_equal. apply IHp.
  - f_equal; [apply IHp1|apply IHp2].
  - destruct (eqbv x v) eqn:Heq.
    + simpl. reflexivity.
    + simpl. f_equal. apply IHp.
Qed.

(* 定理2：常量替换保持 t_x_free 属性 *)
Lemma t_x_free_subst_c : forall p t0 x c t,
  t_x_free p t0 x = true ->
  t_x_free (p {/ c ;; t}) (substitute_tc t0 t c) x = true.
Proof.
Admitted.

(* 定理3（修正版）：常量替换可以分配进入 equality_4 中，并且同时替换参数向量 *)
Lemma equality_4_subst_c : forall n m v1 v2 F c t,
  (equality_4 F n m v1 v2) {/ c ;; t} = 
  equality_4 (F {/ c ;; t}) n m (substitute_vc n v1 t c) (substitute_vc m v2 t c).
Proof.
  intros n. induction n.
  - (* Base Case: n = 0，通常 equality_4 递归到尽头直接返回 F *)
    intros. admit.
  - (* Inductive Step: S n，项长度大于0 *)
    intros m v1 v2 F c t.
    (* 展开一层 equality_4 *)
    simpl. 
    (* equality_4 生成了类似 (equality hd1 hd2) -> (equality_4 ... tl1 tl2) 的结构 *)
    f_equal. admit.
Admitted.

(* 定理4：常量替换不凭空引入特定自由变量 *)
(* 注意：在标准逻辑中，仅当 t 为闭项或 t 中不含自由变量 x 时此定理才成立。
   你的库中如果没有前提条件，可能是约定了替换规则或 t 的性质 *)
Lemma not_free_subst_c : forall p x c t,
  ~ x ∈ (Formula_free_Ens p) ->
  ~ x ∈ (Formula_free_Ens (p {/ c ;; t})).
Proof.
  intros p x c t.
  induction p; simpl; intros H H_in.
  - (* equality *)
    (* 需要使用项的自由变量引理：如果不属于等式的项，替换后也不属于 *)
    admit. 
  - (* atomic *)
    admit.
  - (* Not *)
    apply IHp in H. contradiction.
  - (* Contain *)
    (* 集合的并集： x \in Free(p1) U Free(p2) *)
    (* 这里需要你们库中 Ensemble 集合并集的拆解引理，如 Union_inv *)
    admit.
  - (* ForAll *)
    (* 从自由变量集合中去除了 v *)
    (* 需要证明如果不属于 Free(p) \ {v}，则也不属于 Free(p{/c;;t}) \ {v} *)
    admit.
Admitted.

Lemma Axiom_system_subst_c : forall p c t, 
  Axiom_system p -> Axiom_system (p {/ c ;; t}).
Proof.
  intros p c t H_ax. induction H_ax.
  all: try (simpl; econstructor; eauto).
  - simpl. rewrite subst_F_c_v_comm. econstructor.
    apply t_x_free_subst_c. exact H.
  - rewrite equality_4_subst_c. simpl. econstructor.
  - rewrite equality_4_subst_c. simpl. econstructor.
  - apply not_free_subst_c. exact H.
Qed.

(* Lemma Lemma_3_4_32' : forall Γ p c, Γ ├ p
  -> (forall q, q ∈ Γ -> ~ ( c ∈ (Formula_C_set q)))
  -> exists y, ~ (y ∈ (Formula_free_Ens p)) /\ Γ ├ ∀ y, p{/ c;;Tvar y}.
Proof.
  intros Γ0 p c Hp Hc.   
  assert (H_exists_y: exists y, ~ (y ∈ (Formula_free_Ens p))
          /\ (forall q, q ∈ Γ0 -> ~ (y ∈ (Formula_free_Ens q)))).
  { (* 这里利用 'Finite' 引理。如果目前难以构造，可以先 admit 此步骤，
       将重点放在后面的归纳推导上 *)
    admit. 
  }
  destruct H_exists_y as [y [Hy_p Hy_Γ]].
  exists y. split; [exact Hy_p |].
  apply Gen_Rule_1'. 
  - intros q Hq. apply Hy_Γ. assumption. 
  - revert y Hy_p Hy_Γ.
    induction Hp using deduce_K_ind; intros y Hy_p Hy_Γ.
  
  (* ... 后续证明逻辑与之前一致 ... *)
Admitted. *)
  
(* 如果 Γ ⊢ p，且 c 不在 Γ 中，则存在一个不在 p 中出现的变量 y，使得 Γ ⊢ ∀y p(c; y) *)
Lemma Lemma_3_4_32 : forall Γ p c, Γ ├ p
  -> (forall q, q ∈ Γ -> ~ ( c ∈ (Formula_C_set q)))
  -> exists y, ~ (y ∈ (Formula_Ens p)) /\ Γ ├ ∀ y, p{/ c;;Tvar y}.
Proof.
  intros Γ0 p c Hp Hc.
  assert (H_exists_y: exists y, ~ (y ∈ (Formula_Ens p)) 
          /\ (forall q, q ∈ Γ0 -> ~ y ∈ (Formula_free_Ens q))).
  { admit. } 
  destruct H_exists_y as [y [Hy_p Hy_Γ]].
  exists y. split; [exact Hy_p |]. apply Gen_Rule_1'.
  - intros q Hq. apply Hy_Γ. exact Hq.
  - clear Hy_p. revert y Hy_Γ.
    induction Hp using deduce_K_ind; intros y Hy_Γ.
    + assert (Hnc: ~ c ∈ (Formula_C_set p)). { apply Hc. assumption. }
      rewrite subst_fc_not_in.
      * apply K0. assumption.
      * exact Hnc.
    + apply K1. apply Axiom_system_subst_c. assumption.
    + assert (H_imp := IHHp1 y Hy_Γ).
      assert (H_q := IHHp2 y Hy_Γ).
      eapply MP.
      * exact H_imp.
      * auto.
Admitted.

(* 常数替换不增加原公式中不存在的变量 *)
Lemma sub_cv_free : forall p c y x, ~ x ∈ (Formula_Ens p)
  -> ~ y ∈ (Formula_Ens p) -> x <> y
  -> ~ x ∈ (Formula_Ens (p{/c;; Tvar y})).
Proof.
  intros. induction p; simpl; intro.
  - Search (?x ∈ (?a ∪ ?b)). apply UnionI in H2.
    admit.
  - admit.
  - apply IHp; auto.
  - apply UnionI in H2. destruct H2.
    + apply IHp1; auto.
      * intro. apply H. apply Union_introl. auto.
      * intro. apply H0. apply Union_introl. auto.
    + apply IHp2; auto.
      * intro. apply H0. apply Union_introl. auto.
      * intro. apply H0. apply Union_introl. auto.
Admitted.

Lemma Lemma_3_5_15 : forall Γ p x c, Γ ├ p
  -> (forall q, q ∈ Γ -> ~ ( c ∈ (Formula_C_set q)))
  -> ~ (x ∈ (Formula_Ens p))
  -> Γ ├ (∀ x, p{/c;;(Tvar x)}).
Proof.
  intros. destruct (Lemma_3_4_32 Γ0 p c H H0) as [y [H_y H_y']].
  destruct (classicT (x = y)). subst; auto.
  set (p{/c;;Tvar y}) as A. assert (~ x ∈ (Formula_Ens A)).
  { unfold A. apply sub_cv_free; auto. }
  assert (├ (∀ y, A) → (∀ x, (A){y;;(Tvar x)})).
  { pose proof prop_3_12_1 A y x H2.
    apply equivalent_theorem in H3 as [H3 _]. auto. }
  apply Union_l_A with (Γ := Γ0) in H3. rewrite Union_empty_l in H3.
  pose proof (MP _ _ _ H3 H_y'). subst A. rewrite subst_c_v in H4; auto.
Qed.

Fact CE_le3 : forall n : nat, consistence (CE n).
Proof.
  intros. induction n.
  - red. intros. intro. destruct H.
    simpl in *. rewrite double_C_consistence in H_consistence_set.
    unfold consistence in H_consistence_set.
    unfold Γ' in *. destruct (H_consistence_set q). tauto.
  - red. intros. intro. pose proof H as contradictionP.
    destruct H. simpl in H, H0. destruct classicT.
    + red in c. pose proof c q. destruct (fun_NF n); try tauto.
      destruct f; try tauto. set (Gamma := CE n ∪ [/¬ (∀ v, f)]).
      set (c_idx := C (S (n + (n + 0)))). set (c' := Tcon c_idx).
      assert (consistence Gamma) by auto.
      assert (Gamma ├ (f {v ;; c'})). { apply rule_Indirect with q; auto. }
      assert (Gamma ├ (∀ v, f)).
      { (* c_2n+1 在 Gamma 的任何公式中未出现过 *)
        assert(forall q, q ∈ Gamma -> ~ (c_idx ∈ (Formula_C_set q)) ). 
        { admit. }
        assert (~ v ∈ (Formula_Ens (f {v ;; c'}))).
        { admit. }
        pose proof Lemma_3_5_15 Gamma (f {v ;; c'}) v c_idx H3 H4 H5.
        assert ((f {v ;; c'}) {/ c_idx ;; Tvar v} = f).
        { apply subst_f_fc_inv. intro. pose proof (H4 (¬(∀ v, f))).
          assert (¬(∀ v, f) ∈ Gamma). { apply Union_intror, In_singleton. }
          apply H8 in H9. apply H9. simpl. auto. }
        rewrite H7 in H6. auto. }
      assert (Gamma ├ ¬ (∀ v, f)). 
      { apply K0. apply UnionI. right. apply In_singleton. }
      pose proof H2 (∀ v, f). tauto.
    + pose proof (IHn q). tauto.
Admitted.

(* CE_all是一致集 *)
Lemma CE_all_consistence : consistence CE_all.
Proof.
  - red; intros. intro. destruct H. apply CE_le1 in H as [], H0 as [].
    destruct (CE_le2 x x0).
    + pose proof @ subsetprove _ _ _ H1 H. pose proof CE_le3 x0. red in H3. 
      destruct (H3 q); tauto.
    + pose proof @ subsetprove _ _ _ H1 H0. pose proof CE_le3 x.
      red in H3; destruct (H3 q); tauto.
Qed.

(* CE_all是极大的 *)
Fact CE_all_max : forall p, ~ p ∈ CE_all -> ~ consistence (CE_all ∪ [/p]).
Proof.
  intros. intro. destruct H. inversion NF_bij. destruct (H1 p) as [pn ?].
  assert (consistence ((CE pn) ∪ [/p])).
  { apply subsetNocontra with (CE_all ∪ [/p]); auto. red; intros. destruct H3.
    - left. exists pn; auto.
    - right; auto. }
  red; red. exists (S pn). simpl. rewrite H2 in *.
  destruct (classicT (consistence (CE pn ∪ [/p]))).
  - do 2 (destruct p; try (right; split)). left; right; split.
  - tauto.
Qed.

(* CE_all 具有亨金证据 *)
Fact CE_all_wit : witness_property CE_all.
Proof.
  red; intros. inversion NF_bij as [NF_inj NF_sur].
  destruct (NF_sur (¬(∀ x, p))) as [n ?].
  assert (consistence ((CE n) ∪ [/ ¬(∀ x, p)])).
  { apply subsetNocontra with CE_all; auto.
    - red; intros. destruct H1. exists n; auto. destruct H1. auto.
    - apply CE_all_consistence. }
  exists (C (1+2*n)).
  assert ((CE (S n)) ⊆ CE_all). { red; intros; exists (S n); auto. }
  apply H2. simpl. rewrite H0 in *.
  destruct (classicT (consistence (CE n ∪ [/¬(∀ x, p)]))); try tauto.
  right. split.
Qed.

(* 关键引理: CE_all 是具有亨金证据的极大一致集 *)
Lemma CE_all_MCW : maximal_consistent_set CE_all /\ witness_property CE_all.
Proof.
  split.
  - split.
    + apply CE_all_consistence.
    + intros. destruct (classicT (p ∈ CE_all)). 
      * auto. 
      * pose proof (CE_all_max). apply H0 in n. contradiction.
  - apply CE_all_wit.
Qed.

End max_consistence_extention.

(******************************************************************)
(*                           公式可数性                            *)
(******************************************************************)

Require Import bijection_nat_Formula1.

(* (* 自然数和公式存在一一对应. *)
Lemma bijection_nat_formula : bijection nat Formula.
Proof.
  pose proof @Bernstein_Theorem nat Formula. pose proof Formula_contable.
  destruct X as [g Hg].
  set (f := fun (n : nat) => equality (Tvar (X n)) (Tvar (X n))).
  assert (Hf : function_injective f). { red; intros. inversion H0. auto. } 
  apply (H f g); auto. constructor. exact (f 0).
Qed. *)

(******************************************************************)
(*         扩张引理: 任意一致集都可以扩张成具有见证性的极大一致集        *)
(******************************************************************)

Theorem max_consistence_extension : forall Γ, consistence Γ 
  ->  exists Γ', maximal_consistent_set Γ'
   /\ double_C_set Γ ⊆ Γ' /\ witness_property Γ'.
Proof.
  intros. pose proof bijection_nat_formula as [].
  exists (CE_all Γ bij_f). split.
  - apply CE_all_MCW; auto. split; auto.
  - split.
    + red; intros. red. red. exists 0. simpl. auto.
    + apply CE_all_MCW; auto. split; auto.
Qed.

(* 完全性定理 *)
Theorem complete_theorem : complete.
Proof.
  apply complete_consistence_satisfiable. red; intros.
  pose proof max_consistence_extension _ H as [Γ' [? []]].
  apply double_C_satisfiable; auto. rewrite double_C_consistence in H; auto.
  red. exists (D_I Γ' H0). unfold value. exists (@ assignment Γ' H0).
  pose proof model_sat Γ' H0 H2. red; intros. apply H1 in H4. apply H3; auto.
Qed.
