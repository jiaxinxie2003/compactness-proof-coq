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
Proof. intros. induction v. auto. simpl. f_equal. Qed.

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
  intros. induction v. auto. simpl. f_equal.
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

