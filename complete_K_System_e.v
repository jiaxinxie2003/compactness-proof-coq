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
Require Import complete_K_System_s.
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

(* (* 在项t中把常元x替换成t': tc(x;t') *)
Fixpoint substitute_tc (t t': term) (x: Con) :=
  match t with
  | Tcon c => if (eqbc x c) then t' else Tcon c
  | Tvar y => Tvar y
  | Tfun  _ q => let fix substitute_vc (n: nat) (r: Vector.t (term) n)
                   (t': term) (x: Con) :=
                   match r with 
                   | [] => []
                   | h :: q => (substitute_tc h t' x) :: (substitute_vc _ q t' x) 
                   end in (Tfun _ (substitute_vc _ q t' x))
  end. *)

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

(* 连续代换 ϕ(c; y)(y; x) = ϕ(c; x) *)
Lemma subst_c_v : forall p c y x, ~ (y ∈ (Formula_Ens p))
  -> (p{/ c ;; Tvar y}){y ;; Tvar x} = p{/ c ;; Tvar x}.
Proof. admit. Admitted.

(* 如果 Γ ⊢ ϕ，且 c 不在 Γ 中，则存在一个不在 ϕ 中出现的变量 y，使得 Γ ⊢ ∀y ϕ(c; y) *)
Lemma Lemma_3_4_32 : forall Γ p c, Γ ├ p
  -> (forall q, q ∈ Γ -> ~ ( c ∈ (Formula_C_set q)))
  -> exists y, ~ (y ∈ (Formula_Ens p)) /\ Γ ├ ∀ y, p{/ c;;Tvar y}.
Proof.
  intros.
Admitted.

Lemma Lemma_3_5_15 : forall Γ p x c, Γ ├ p
  -> (forall q, q ∈ Γ -> ~ ( c ∈ (Formula_C_set q)))
  -> t_x_free p (Tcon c) x = true
  -> Γ ├ (∀ x, p{/c;;(Tvar x)}).
Proof.
  intros. destruct (Lemma_3_4_32 Γ0 p c H H0) as [y [H_y H_y']].
  set (p{/c;;Tvar y}) as A.
  assert (~ x ∈ (Formula_Ens A)). admit.
  assert (├ (∀ y, A) → (∀ x, (A){y;;(Tvar x)})).
    { pose proof prop_3_12_1 A y x H2.
      apply equivalent_theorem in H3 as [H3 _]. auto. }
  apply Union_l_A with (Γ := Γ0) in H3. rewrite Union_empty_l in H3.
  pose proof (MP _ _ _ H3 H_y'). subst A. rewrite subst_c_v in H4; auto.
Admitted.


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
      set (c' := Tcon (C (S (n + (n + 0))))). assert (consistence Gamma) by auto.
      assert (Gamma ├ (f {v ;; c'})). { apply rule_Indirect with q; auto. }
      assert (Gamma ├ (∀ v, f)).
      { pose proof Lemma_3_5_15 Gamma ((f) {v;; c'}) v (C (S (n + (n + 0)))) H3.

assert( forall q, q ∈ Gamma -> ~ (C (S (n + (n + 0)))) ∈ (Formula_C_set q) ). admit.
 admit. }
      assert (Gamma ├ ¬ (∀ v, f)). { apply K0, UnionI. right. apply In_singleton. }
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
  - destruct p.
    + right; split.
    + right; split.
    + destruct p.
      * right; split.
      * right; split.
      * right; split.
      * right; split.
      * left; right; split.
    + right; split.
    + right; split.
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

Require Import bijection_nat_Formula_K_System.

(* Check Countable. *)
Print Formula.

Lemma Con_countable : Countable Con.
Proof.
  apply (@bijection_Countable _ nat); solve_Countable. apply bijection_sym.
  apply (Build_bijection _ _ (fun x => (C x))).
  + hnf; intros. inversion H; auto.
  + hnf; intros. destruct b. exists n. auto.
Qed.

Lemma Var_countable : Countable Var.
Proof.
  apply (@bijection_Countable _ nat); solve_Countable. apply bijection_sym.
  apply (Build_bijection _ _ (fun x => (X x))).
  + hnf; intros. inversion H; auto.
  + hnf; intros. destruct b. exists n. auto.
Qed.

Fact Fun_countable : Countable Fun.
Proof.
  pose proof natnat_nat_bijection.
  assert (bijection Fun (nat * nat)).
  { set (F1 f := match f with | F a b => a end).
    set (F2 f := match f with | F a b => b end).
    apply (Build_bijection _ _ (fun f => (pair (F1 f) (F2 f)))).
    + hnf; intros. inversion H0. destruct a1,a2. simpl in H2,H3.
      inversion H3. subst; auto.
    + hnf; intros. destruct b. exists (F n n0). simpl; auto. }
  apply bijection_injection in H,H0.
  assert (injection Fun nat). { apply (@injection_trans _ (nat * nat)); auto. }
  apply (@injection_Countable _ nat); auto. apply nat_Countable.
Qed.

(* 如果 A 是可数的，那么 A 的 n 维向量也是可数的 *)
Lemma vector_countable : forall A n, Countable A -> Countable (Vector.t A n).
Proof.
  intros. induction n.
(*   - (* Base Case: 0 维向量同构于 unit *)
    apply (@bijection_Countable _ unit); [solve_Countable |].
    apply (Build_bijection _ _ (fun _ => Vector.nil A)).
    + hnf; intros. destruct a1 using case0, a2 using case0. auto.
    + hnf; intros. exists (Vector.nil A). destruct b. auto. 
  - (* Inductive Step: S n 维向量同构于 A * Vector A n *)
    apply (@bijection_Countable _ (A * Vector.t A n)); [| apply bijection_sym].
    + apply prod_Countable; auto.
    + apply (Build_bijection _ _ (fun v => (Vector.hd v, Vector.tl v))).
      * hnf; intros. simpl in H. injection H; intros.
        apply (Vector.eta a1). rewrite H0, H1. apply (Vector.eta a2).
      * hnf; intros. destruct b as [h t].
        exists (Vector.cons _ h _ t). auto. *)
Admitted.

Lemma Rel_countable : Countable Rel.
Proof.
  apply (@bijection_Countable _ nat); solve_Countable. apply bijection_sym.
Admitted.

Lemma term_countable : Countable term.
Proof. red.
Admitted.

Lemma equality_countable : Countable (term -> term -> Formula).
Proof.
Admitted.

Lemma atomic_countable : Countable (forall r, t term (arity_R r) -> Formula).
Admitted.

Lemma complexityF_countable_lemma :
  Countable (sig (fun x : Formula => formula_complexity x <= 0)).
Proof.
  assert (Countable (sig (fun x : Formula
    => (exists t1 t2, x = equality t1 t2)))). admit.
  assert (Countable (sig (fun x : Formula => (exists r H, x = atomic r H)))). admit.
  assert ((sig (fun x : Formula => (exists t1 t2, x = equality t1 t2)))
    + (sig (fun x : Formula => (exists r H, x = atomic r H)))
    = (sig (fun x : Formula => formula_complexity x <= 0)))%type.
  admit.
Admitted.

(* 对于任意自然数n, 复杂度小于等于n的公式的全体是可数的 *)
Lemma complexityF_countable : forall n,
  Countable (sig (fun x: Formula => formula_complexity x <= n)).
Proof.
  induction n.
  - eapply complexityF_countable_lemma; eauto.
  - set (s := sig (fun x => formula_complexity x <= n)).
    apply (@injection_Countable _ (nat + s + s * s)%type); [| solve_Countable].
    assert (bijection nat (nat + s + s * s)).
    { pose proof @Bernstein_Theorem nat (nat + s + s * s).
      assert (Countable (nat + s + s * s)).
      { apply sum_Countable. apply sum_Countable; auto. apply nat_Countable.
        apply prod_Countable; auto. } destruct X.
      set (x1 m := (equality (Tvar (X m)) (Tvar (X m)))).
      assert (forall m, formula_complexity (x1 m) <= n). { simpl. lia. }
      set (s1 m := @exist Formula (fun x => formula_complexity x <= n) (x1 m) (H0 m)).
      assert (@function_injective nat (nat + s + s * s)
        (fun (n : nat) => @inl (nat + s) (s * s) (@inl nat s n))).
      { hnf; intros. inversion H1; auto. }
      apply (H _ _ H1 in_inj). constructor.
      exact (@inl (nat + s) (s * s) (@inl nat s 0)). }
Admitted.

(* Formula是可数的. *)
Theorem Formula_contable : Countable Formula.
Proof.
  apply (@injection_Countable _ (sigT (fun n => sig (fun x => formula_complexity x <= n)))).
  - apply (Build_injection _ _ 
    (fun x0 => existT (fun n => sig (fun x => formula_complexity x <= n)) (formula_complexity x0)
    (exist (fun x => formula_complexity x <= formula_complexity x0) x0 (le_n (formula_complexity x0))))).
    hnf; intros. inversion H. auto.
  - solve_Countable. apply complexityF_countable.
Qed.

(* 自然数和公式存在一一对应. *)
Theorem bij_NF : bijection nat Formula.
Proof.
  pose proof @Bernstein_Theorem nat Formula. pose proof Formula_contable.
  destruct X.
Admitted.

(******************************************************************)
(*         扩张引理: 任意一致集都可以扩张成具有见证性的极大一致集        *)
(******************************************************************)

Theorem max_consistence_extension : forall Γ, consistence Γ 
  ->  exists Γ', maximal_consistent_set Γ' 
        /\ double_C_set Γ ⊆ Γ' /\ witness_property Γ'.
Proof.
  intros. pose proof bij_NF as bNF. destruct bNF.  exists (CE_all Γ bij_f). split.
  - apply CE_all_MCW; auto. auto. split; auto.
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
