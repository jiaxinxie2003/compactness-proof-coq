Require Import base_pc.
Require Import formulas_K_System.
Require Import syntax_K_System.
Require Import semantic_K_System.
Require Import soundness_K_System.
Require Import complete_K_System_s.
Require Import Mappings.
Require Import complete_K_System'.

Require Import Coq.Vectors.Vector.
Import VectorNotations.
Require Import Coq.micromega.Lia.

(**************************************************************************)
(*       在扩张了常量的一阶语言中，将一致集Γ逐步扩张为一个极大一致集Γ'            *)
(**************************************************************************)
Section max_consistence_extention.
Variable Γ: Ensemble Formula.
Hypothesis H_consistence_set : consistence Γ.
(* 记 double_C_set Γ 为 Γ' *)
Let Γ' := double_C_set Γ.
(* 自然数集到公式集的双射 fun_NF *)
Variable fun_NF : nat -> Formula.
Hypothesis NF_bij : function_bijective fun_NF.

(* 计算项 (term) 中出现的最大常元下标 *)
Fixpoint max_c_term t :=
  match t with
  | Tcon c => match c with C n => n end
  | Tvar y => 0
  | Tfun _ q => let fix max_c_vc (n: nat) (r: Vector.t term n) :=
                  match r with 
                  |[] => 0
                  | h :: q' => max (max_c_term h) (max_c_vc _ q') 
                  end in (max_c_vc _ q)
  end.

Fixpoint max_c_vc n r :=
  match r with
  |[] => 0
  | h :: q' => max (max_c_term h) (max_c_vc _ q') 
  end.

(* 计算公式 (Formula) 中出现的最大常元下标 *)
Fixpoint max_c_formula p :=
  match p with 
  | equality t1 t2 => max (max_c_term t1) (max_c_term t2)
  | atomic _ q => max_c_vc _ q
  | Not q => max_c_formula q
  | Contain m n => max (max_c_formula m) (max_c_formula n)
  | ForAll x q => max_c_formula q
  end.

(* 算出前 n 个公式里的常元最大下标 *)
Fixpoint max_c_formula_up_to n :=
  match n with
  | O => max_c_formula (fun_NF O)
  | S n' => max (max_c_formula (fun_NF (S n'))) (max_c_formula_up_to n')
  end.

(* 动态生成第 n 步所需的新奇数常元下标 *)
Definition fresh_odd_c n := 1 + 2 * (max_c_formula_up_to n + n).

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
                                 ∪ [/ Not (p {x;;(Tcon (C (fresh_odd_c n')))})]
                        | _ => (CE n') ∪ [/ (fun_NF n')]
                        end
            end
  end.

(* CE_all = ∪ (CE i) *)
Definition CE_all : Ensemble Formula := fun p => exists n, p ∈ (CE n).

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

Fact union_complement_equiv': forall (A B: Ensemble Con) x,
  (~ x ∈ (A ∪ B)) <-> (~ x ∈ A) /\ (~ x ∈ B).
Proof.
  split; intro.
  - split; red; intro; destruct H; ES.
  - destruct H. red. intro. destruct H1; contradiction.
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
    destruct (eqbc_reflect c c_con) as [Heg | Hneq]; auto.
    subst. elim Hnot. apply Single. auto.
  - simpl. simpl in Hnot. f_equal. revert Hnot.
    induction v_vec as [| h n q IHq]. intro. auto. intro. f_equal.
    + apply IH. intro. apply Hnot. left. auto.
    + apply IHq. intro. apply Hnot. right. auto.
Qed.

(* 引理 2：针对 Vector 的常量集和替换 *)
Lemma subst_vc_not_in : forall n (v : Vector.t term n) c t',
  ~ c ∈ (Vector_C_set n v) -> substitute_vc n v t' c = v.
Proof.
  induction v; intros c t' Hnot.
  - simpl. reflexivity.
  - simpl. f_equal.
    + apply subst_tc_not_in. intro. apply Hnot. simpl. left. auto.
    + apply IHv. intro. apply Hnot. right. auto.
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

(* 如果 Γ ⊢ p，且 c 不在 Γ 中，则存在一个不在 p 中出现的变量 y，使得 Γ ⊢ ∀y p(c; y) *)
Lemma Lemma_3_4_32 : forall Γ p c, Γ ├ p
  -> (forall q, q ∈ Γ -> ~ (c ∈ (Formula_C_set q)))
  -> exists y, Γ ├ ∀ y, p{/ c;;Tvar y}.
Proof.
  intros Γ0 p c Hp Hc.
  assert (H_exists_y: exists y, (forall q, q ∈ Γ0 -> ~ y ∈ (Formula_free_Ens q))).
  { admit. } 
  destruct H_exists_y as [y Hy_Γ].
  exists y. apply Gen_Rule_1'; auto.
  revert y Hy_Γ.
  induction Hp using deduce_K_ind; intros y Hy_Γ.
  + assert (Hnc: ~ c ∈ (Formula_C_set p)). { apply Hc. assumption. }
    rewrite subst_fc_not_in.
    * apply K0. assumption.
    * exact Hnc.
  + (* 情况 2: p 是公理 *)
    (* 需要引理：公理对常量替换封闭 *)
    (* Search (Axiom_system (_ {/ _ ;; _ })) *)
    apply K1. 
    (* apply Axiom_system_subst_c; assumption. *)
    admit.
  + eapply MP. apply IHHp1. auto. apply IHHp2. auto.
Admitted.

Lemma not_in_term_subst : forall t t' x, ~ x ∈ (term_Ens t')
  -> ~ x ∈ (term_Ens (t {x;t'})).
Proof.
  fix IH 1. intros. destruct t.
  - simpl. destruct (eqbv x v) eqn:E; simpl; Eqbv; intro; ES.
    apply Single in H0. contradiction.
  - simpl. intro. destruct H0.
  - simpl. intro. induction t; simpl; intros. destruct H0.
    apply UnionI in H0 as []. apply IH in H0; auto. apply IHt. auto.
Qed.

(* 向量项替换引理 *)
Lemma not_in_vector_subst : forall n v t' x, ~ x ∈ (term_Ens t')
  -> ~ x ∈ (Vector_Ens n (substitute_v n v t' x)).
Proof.
  induction v; simpl; intros. intro. destruct H0.
  apply union_complement_equiv. split. apply not_in_term_subst. auto.
  apply IHv. auto.
Qed.

(* 公式替换引理 *)
Lemma not_in_Formula_subst : forall p t' x, ~ x ∈ (term_Ens t')
  -> ~ x ∈ (Formula_free_Ens (p {x;; t'})).
Proof.
  intros. induction p; simpl; intros; auto.
  - apply union_complement_equiv; split; eapply not_in_term_subst; eauto.
  - eapply not_in_vector_subst in H; eauto.
  - apply union_complement_equiv. auto.
  - destruct (eqbv x v) eqn:E; simpl; intro; destruct H0 as []. Eqbv.
    elim H1. apply Single. auto. contradiction.
Qed.

(* (* 辅助引理：项的常元替换对变量的影响 *)
Lemma not_in_term_free_subst_c : forall t c y x,
  ~ x ∈ (term_Ens t) -> x <> y ->
  ~ x ∈ (term_Ens (substitute_tc t (Tvar y) c)).
Proof.
  induction t; intros; simpl in *; auto.
  - destruct (eqbc c0 c) eqn:E; auto. simpl. intro. apply Single in H1. auto.
  - intro H_in. revert H_in. induction t; simpl; intros H_in; auto.
Admitted.

(* 主引理：公式的常元替换不引入除了 y 以外的新自由变量 *)
Lemma not_in_Formula_free_subst_c : forall p c y x,
  ~ x ∈ (Formula_free_Ens p) ->
  x <> y ->
  ~ x ∈ (Formula_free_Ens (p{/c;; Tvar y})).
Proof.
  induction p; intros c y x H_nx H_neq; simpl in *; auto.
  - (* equality *)
    apply union_complement_equiv in H_nx as [H1 H2].
    apply union_complement_equiv. split.
    + eapply not_in_term_free_subst_c; eauto.
    + eapply not_in_term_free_subst_c; eauto.
  - (* atomic *)
    (* 对向量处理，利用 not_in_term_free_subst_c *)
    admit.
  - (* Contain *)
    apply union_complement_equiv in H_nx as [H1 H2].
    apply union_complement_equiv. split; auto.
  - (* ForAll *)
    (* 常元替换不涉及绑定变量的冲突，所以直接进入内部 *)
    (* H_nx : x ∈ (Formula_free_Ens p ~ [/v]) *)
    intro H_in. 
    (* 根据自由变量集定义，x 必须属于内部且不等于 v *)
    destruct H_in as [H_in_inner H_nv].
    eapply IHp in H_in_inner; eauto. intro. elim H_nx. split; auto.
Admitted. *)

Lemma Lemma_3_5_15 : forall Γ p x c, Γ ├ p
  -> (forall q, q ∈ Γ -> ~ ( c ∈ (Formula_C_set q)))
  -> ~ (x ∈ (Formula_free_Ens p))
  -> Γ ├ (∀ x, p{/c;;(Tvar x)}).
Proof.
  intros. destruct (Lemma_3_4_32 Γ0 p c H H0) as [y H_y'].
  destruct (classicT (x = y)). subst; auto.
  set (p{/c;;Tvar y}) as A. assert (~ x ∈ (Formula_free_Ens A)).
  { (* eapply not_in_Formula_free_subst_c; eauto. *) admit. }
  assert (├ (∀ y, A) → (∀ x, (A){y;;(Tvar x)})).
  { admit. }
  apply Union_l_A with (Γ := Γ0) in H3. rewrite Union_empty_l in H3.
  pose proof (MP _ _ _ H3 H_y'). subst A. rewrite subst_c_v in H4; auto.
Admitted.

(**************************************************************************)

Lemma fresh_c_bound : forall n, max_c_formula (fun_NF n) < fresh_odd_c n.
Proof.
  intros. assert (max_c_formula (fun_NF n) <= max_c_formula_up_to n).
  { destruct n; simpl; lia. } unfold fresh_odd_c. lia.
Qed.

Lemma max_c_term_bound : forall t c_n,
  (C c_n) ∈ (term_C_set t) -> c_n <= max_c_term t.
Proof.
  fix IH 1. intros t c_n H. destruct t.
  - simpl in H. inversion H.
  - simpl in *. destruct c as [n]. inversion H; subst. lia.
  - simpl in *. revert H. induction t; simpl; intros.
    + inversion H.
    + apply UnionI in H. destruct H as [Hin_h | Hin_q].
      * apply IH in Hin_h. apply Nat.le_trans with (max_c_term h). auto.
        apply Nat.le_max_l.
      * apply IHt in Hin_q. apply Nat.le_trans with
        (let fix max_c_vc n r := match r with
                                | [] => 0
                                | h0 :: q' => Init.Nat.max (max_c_term h0) (max_c_vc _ q')
                                end in max_c_vc n t).
        auto. apply Nat.le_max_r.
Qed.

Lemma max_c_formula_bound : forall p c_n, 
  (C c_n) ∈ (Formula_C_set p) -> c_n <= max_c_formula p.
Proof.
  induction p; intros c_n H; simpl in *; auto.
  - apply UnionI in H as []; apply max_c_term_bound in H; lia.
  - revert H. induction t; intros.
    + inversion H.
    + simpl in *. apply UnionI in H as [].
      * apply max_c_term_bound in H. lia.
      * apply IHt in H. lia.
  - apply UnionI in H as []; [apply IHp1 in H | apply IHp2 in H]; lia.
Qed.

Lemma double_C_term_even : forall t c_n,
  (C c_n) ∈ (term_C_set (double_C_term t)) -> exists k, c_n = 2 * k.
Proof.
  fix IH 1. intros t c_n H. destruct t.
  - simpl in H. inversion H.
  - simpl in H. destruct c as [m]. inversion H; subst. exists m. auto.
  - simpl in H. revert H. induction t; simpl; intros. inversion H.
    apply UnionI in H as []. apply IH in H. auto.
    apply IHt in H. auto.
Qed.

Lemma Gamma_prime_even : forall q c_n, 
  q ∈ Γ' -> (C c_n) ∈ (Formula_C_set q) -> exists k, c_n = 2 * k.
Proof.
  intros. inversion H; subst. clear H H1. revert c_n H0.
  induction p; intros; simpl in H0; try (eapply IHp; eauto).
  - apply UnionI in H0 as []; eapply double_C_term_even; eauto.
  - revert c_n H0. induction t; intros; simpl in H0. inversion H0.
    apply UnionI in H0 as []. eapply double_C_term_even; eauto.
    eapply IHt; eauto.
  - apply UnionI in H0 as []. eapply IHp1; eauto. eapply IHp2; eauto.
Qed.

Lemma CE_S_inversion : forall n q,
  q ∈ (CE (S n)) ->
  (q ∈ (CE n)) \/ 
  (q = fun_NF n) \/ 
  (exists p x, fun_NF n = Not (ForAll x p) /\ q = Not (substitute_f p (Tcon (C (fresh_odd_c n))) x)).
Proof.
  intros n q H. simpl in H. destruct classicT.
  - destruct (fun_NF n) eqn:Enf;
    try (inversion H; subst; [left; auto | right; left; inversion H0; auto]).
    destruct f eqn:Ef;
    try do 4 (inversion H; subst; [left; auto | right; left; inversion H0; auto]).
    inversion H. inversion H0. subst; auto.
    apply Single in H2. right. left. auto. apply Single in H0. right. right.
    exists f0,v. auto.
  - left. auto.
Qed.

Lemma CE_elements_source : forall n q, q ∈ (CE n)
  -> (q ∈ Γ') \/ (exists i, i < n /\ q = fun_NF i)
  \/ (exists i p x, i < n /\ fun_NF i = Not (ForAll x p) /\
                 q = Not (substitute_f p (Tcon (C (fresh_odd_c i))) x)).
Proof.
  induction n; intros. simpl in H; auto.
  apply CE_S_inversion in H as [H|[]].
  - apply IHn in H as []; auto. destruct H as [[i[]]|].
    right. left. exists i; auto. do 4 destruct H.
    right. right. exists x,x0,x1; auto.
  - right. left. exists n. auto.
  - right. right. destruct H as [p[]]. exists n,p,x; auto.
Qed.

Lemma max_c_formula_up_to_mono : forall n i,
  n <= i -> max_c_formula_up_to n <= max_c_formula_up_to i.
Proof.
  intros. induction H. auto. simpl.
  assert (max_c_formula_up_to m
   <= Nat.max (max_c_formula (fun_NF (S m))) (max_c_formula_up_to m)).
  { apply Nat.le_max_r. } lia.
Qed.

Lemma fresh_c_mono : forall i j, i < j -> fresh_odd_c i < fresh_odd_c j.
Proof.
  intros. unfold fresh_odd_c. assert (i <= j) by lia.
  pose proof (max_c_formula_up_to_mono i j H0). lia.
Qed.

Lemma C_in_subst_term : forall t1 t2 x c_n,
  (C c_n) ∈ (term_C_set (t1{x;t2})) ->
  (C c_n) ∈ (term_C_set t1) \/ (C c_n) ∈ (term_C_set t2).
Proof.
  fix IH 1. intros. destruct t1; simpl in H.
  - destruct (eqbv x v) eqn:E; auto.
  - inversion H. left. simpl. apply Single. auto.
  - assert (H_vec : forall n v,
      (C c_n) ∈ (Vector_C_set n (substitute_v n v t2 x)) ->
      (C c_n) ∈ (Vector_C_set n v) \/ (C c_n) ∈ (term_C_set t2)).
    { induction v; intros; simpl in H0; auto. apply UnionI in H0 as [].
      + apply IH in H0 as []; auto. left. simpl. left. auto.
      + apply IHv in H0 as []; auto. left. simpl. right. auto. }
    apply H_vec in H as []; auto.
Qed.

Lemma C_in_subst : forall p t x c_n,
  (C c_n) ∈ (Formula_C_set (p{x;; t})) ->
  (C c_n) ∈ (Formula_C_set p) \/ (C c_n) ∈ (term_C_set t).
Proof.
  induction p; intros; simpl in H.
  - apply UnionI in H as []; apply C_in_subst_term in H as []; auto.
    left. simpl. left. auto. left. simpl. right. auto.
  - assert (H_vec : forall n v,
      (C c_n) ∈ (Vector_C_set n (substitute_v n v t0 x)) ->
      (C c_n) ∈ (Vector_C_set n v) \/ (C c_n) ∈ (term_C_set t0)).
    { induction v; intros; auto. simpl in H0. apply UnionI in H0 as [].
      apply C_in_subst_term in H0 as []; auto. left. simpl. left. auto.
      apply IHv in H0 as []; auto. left. simpl. right. auto. }
    apply H_vec in H as []; auto.
  - apply IHp in H as []; auto.
  - apply UnionI in H as []; auto.
    apply IHp1 in H as []; auto. left. simpl. left. auto.
    apply IHp2 in H as []; auto. left. simpl. right. auto.
  - destruct (eqbv x v) eqn:E; auto. apply IHp in H as []; auto.
Qed.

Lemma CE_no_fresh_c : forall n q,
  q ∈ (CE n) -> ~ (C (fresh_odd_c n)) ∈ (Formula_C_set q).
Proof.
  intros. apply CE_elements_source in H as [H |[]].
  - intro. apply Gamma_prime_even in H0 as []; auto. unfold fresh_odd_c in H0. lia.
  - destruct H as [i []]. subst q. intro. apply max_c_formula_bound in H0.
    pose proof fresh_c_bound i. apply fresh_c_mono in H. lia.
  - destruct H as [i [p [x [H [Hn Hq]]]]]. subst q. simpl. intro.
    apply C_in_subst in H0 as [].
    + assert ((C (fresh_odd_c n)) ∈ (Formula_C_set (fun_NF i))).
      { rewrite Hn. simpl. auto. }
      apply max_c_formula_bound in H1.
      pose proof (fresh_c_bound i). apply fresh_c_mono in H. lia.
    + simpl in H0. apply Single in H0. apply fresh_c_mono in H. inversion H0.
      unfold fresh_odd_c in H. lia.
Qed.

Lemma fresh_c_not_in_CE : forall n q, q ∈ (CE n ∪ [/ (fun_NF n)])
  -> ~ (C (fresh_odd_c n)) ∈ (Formula_C_set q).
Proof.
  intros. destruct H.
  - eapply CE_no_fresh_c; eauto.
  - inversion H. intro. apply max_c_formula_bound in H1.
    pose proof (fresh_c_bound n). rewrite H0 in *. lia.
Qed.

Fact CE_le3 : forall n : nat, consistence (CE n).
Proof.
  intros. induction n.
  - simpl. rewrite double_C_consistence in H_consistence_set. unfold Γ'. auto.
  - red. intros q H_contra. simpl in H_contra. destruct classicT as [Hc | Hnc].
    + pose proof Hc. red in H. specialize H with q.
      destruct (fun_NF n) eqn:E_funNF; try tauto.
      destruct f eqn:E_f; try tauto. subst f. clear H.
      set (Gamma := CE n ∪ [/¬ (∀ v, f0)]) in *.
      (* 要添加的新见证常元项 *)
      set (c' := Tcon (C (fresh_odd_c n))) in *.
      assert (Gamma ├ ¬ (∀ v, f0)).
      { apply K0. apply UnionI. right. apply In_singleton. }
      assert (Gamma ├ (∀ v, f0)).
      { assert (Gamma ├ (f0 {v ;; c'})).
        { destruct H_contra. apply (rule_Indirect _ _ _ H0 H1). }
        assert (forall q, q ∈ Gamma -> ~ (C (fresh_odd_c n) ∈ (Formula_C_set q))).
        { intros. apply (fresh_c_not_in_CE n q0). rewrite E_funNF. auto. }
        assert (~ v ∈ (Formula_free_Ens (f0 {v ;; c'}))).
        { apply not_in_Formula_subst. unfold c'. simpl. intro. inversion H2. }
        assert ((f0 {v ;; c'}) {/ (C (fresh_odd_c n)) ;; Tvar v} = f0).
        { apply subst_f_fc_inv. intro. pose proof (H1 (¬(∀ v, f0))).
          assert (¬(∀ v, f0) ∈ Gamma). { apply Union_intror, In_singleton. }
          apply H4 in H5. apply H5. simpl. auto. }
        pose proof Lemma_3_5_15 Gamma (f0 {v ;; c'}) v (C (fresh_odd_c n)) H0 H1 H2.
        rewrite H3 in H4. auto. }
      pose proof Hc (∀ v, f0). tauto.
    + pose proof (IHn q). tauto.
Qed.

(**************************************************************************)

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
  exists (C (fresh_odd_c n)).
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