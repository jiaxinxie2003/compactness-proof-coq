(**************************************************************************)
(*  This is part of bijection, it is distributed under the terms of the   *)
(*            GNU Lesser General Public License version 3                 *)
(*               (see file LICENSE for more details)                      *)
(*                                                                        *)
(*                       Copyright 2023-2028                              *)
(*         Dakai Guo, qiming Wang, jianghao Liu and Wensheng Yu           *)
(**************************************************************************)

(** bijection_nat_Formula1 *)

Require Import Mappings.
Require Import base_pc.
Require Import formulas_K_System.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Epsilon.
Require Import Coq.micromega.Lia.
(*Print epsilon_statement.*)

Theorem classicT : forall (P: Prop), {P} + {~P}.
Proof.
  intros. assert {x:bool | if x then P else ~P}.
  { apply constructive_indefinite_description. destruct (classic P).
    - exists true. auto.
    - exists false. auto. }
  destruct H, x; auto.
Qed.

(*Inductive function_bijective {A B} (f: A -> B): Prop :=
  | fun_bij_intro : function_injective f ->
                    function_surjective f -> function_bijective f.*)

(* 像集 *)
Inductive image_set {A B : Type} (f : A -> B)  (X: Ensemble A) : Ensemble B :=
  image_intro : forall a, a ∈ X -> (f a) ∈ (image_set f X).

(* 反函数 *)
Definition function_rev {A B : Type} (f : A -> B) (g : B -> A) := 
  forall x, g (f x) = x.

(* 根据f构造反函数 *)
Definition fun_rev {A B : Type} (f : A -> B) (a: A) (y:B) : A :=
  match (classicT (exists x, f x = y)) with
  | left l => proj1_sig (constructive_indefinite_description _ l)
  | right _ => a
  end.

(* 引理：如果A非空,f是A到B的单射函数,则f存在反函数  *)
Lemma injection_funrev : forall {A B : Type} (f : A -> B),
  inhabited A -> function_injective f -> exists g, function_rev f g.
Proof.
  intros. destruct H. exists (fun_rev f X).
  red; intros. unfold fun_rev. destruct classicT.
  - destruct constructive_indefinite_description. simpl. auto.
  - destruct n. eauto.
Qed.

Section bernstein.

Context {A B : Type} (f : A -> B) (g : B -> A).
Hypothesis Inj_f : function_injective f.
Hypothesis Inj_g : function_injective g.
Hypothesis Inhabited_B : inhabited B.

(* 令C_0=A \g[B], C_(n+1)=g[f[C_n ]] *)
Fixpoint Cn n : Ensemble A :=
  match n with
  | O => Complement _ (image_set g (Full_set B))
  | S n' => image_set g (image_set f (Cn n'))
  end.

(* 并令C=⋃_(n=0)^∞ C_n *)
Let Cset : Ensemble A := fun x => exists n, x ∈ (Cn n).

Let g_rev := proj1_sig (constructive_indefinite_description _ 
             (injection_funrev g Inhabited_B Inj_g)).
(* h(a) *)
Let h a :=
  match (classicT (a∈Cset)) with
  | left _ => f a
  | right _ => g_rev a
  end.

(* h是双射 *)
Lemma Bernstein : function_bijective h.
Proof.
  assert (grev : forall x, g_rev (g x) = x).
  { intros. unfold g_rev. destruct constructive_indefinite_description.
    simpl. apply f0. }
  assert (in_cset : forall x, ~ x ∈ Cset -> exists y, x = g y).
  { intros. destruct (classic (exists y, x = g y)); auto. destruct H. red; 
    red. exists 0. red; red; red. intro. induction H. destruct H0; eauto. }
  split.
  - hnf; intros. unfold h in H. destruct classicT, classicT.
    + apply Inj_f; auto.
    + assert (g (f a1)= a2). 
      { pose proof in_cset _ n as [y ?]. rewrite H0 in H. rewrite grev in H. 
        destruct i. destruct n. red; red. exists (S x). simpl. 
        rewrite H0, <- H. repeat apply image_intro. auto. } 
      destruct i. destruct n. red; red. exists (S x). simpl.
      rewrite <-H0. apply image_intro. apply image_intro. auto.
    + assert (g (f a2) = a1).
      { destruct (classic (exists y, a1 = g y)).
        - destruct H0 as [y ?]. rewrite H0 in H. rewrite grev in H. subst; auto.
        - destruct n. red; red. exists 0. red; red; red. intro.
          destruct H0. induction H1; eauto. }
      destruct i. destruct n. red; red. exists (S x). simpl. 
      rewrite <- H0. repeat apply image_intro. auto.
    + pose proof in_cset _ n as [y1 ?]; pose proof in_cset _ n0 as [y2 ?].
      subst. rewrite grev in H, H. f_equal; auto.
  - hnf; intros. destruct (classic (b ∈ (image_set f Cset))).
    + induction H. unfold h. exists a. destruct classicT; tauto.
    + assert (~(g b) ∈ Cset).
      { intro. destruct H0. destruct x.
        - simpl in H0. red in H0. red in H0. destruct H0.
          apply image_intro; auto. constructor.
        - simpl in H0. destruct (classic (b ∈ (image_set f (Cn x)))).
          + destruct H. induction H1. constructor. red; red. eauto.
          + remember (g b). induction H0. apply Inj_g in Heqa. subst; tauto. }
      exists (g b). unfold h. destruct classicT. tauto. rewrite grev. auto.
Qed.

(* 伯恩斯坦定理 *)
Theorem Bernstein_Theorem : bijection A B.
Proof.
  apply (Build_bijection _ _ h); apply Bernstein.
Qed.

End bernstein.

(* 定义公式的复杂度(逻辑深度) *)
Fixpoint formula_complexity (p: Formula) : nat :=
  match p with
  | equality _ _ => 0
  | atomic _ _ => 0
  | Not q => S (formula_complexity q)
  | Contain q r => S (max (formula_complexity q) (formula_complexity r))
  | ForAll _ q => S (formula_complexity q)
  end.

(* (* 辅助引理：替换不增加复杂度 *)
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
Qed. *)


(* (* 公式集可数 *)
(* 对于任意自然数n, 层数小于等于n的公式的全体是可数的. *)
Fixpoint rankF (p:Formula): nat :=
  match p with
  | X _ => 0
  | Not x => 1 + rankF x
  | Contain x y => 1 + rankF x + rankF y
  end. *)

(* Check Countable. *)
Print Formula.

Fact Con_countable : Countable Con.
Proof.
  apply (@bijection_Countable _ nat); solve_Countable. apply bijection_sym.
    apply (Build_bijection _ _ (fun x => (C x))).
    + hnf; intros. inversion H; auto.
    + hnf; intros. destruct b. exists n. auto.
Qed.

Fact Var_countable : Countable Var.
Proof.
  apply (@bijection_Countable _ nat); solve_Countable. apply bijection_sym.
    apply (Build_bijection _ _ (fun x => (X x))).
    + hnf; intros. inversion H; auto.
    + hnf; intros. destruct b. exists n. auto.
Qed.

Print Fun.

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

Fact Rel_countable : Countable Rel.
Proof.
  pose proof natnat_nat_bijection.
  assert (bijection Rel (nat * nat)).
  { set (R1 r := match r with | R a b => a end).
    set (R2 r := match r with | R a b => b end).
    apply (Build_bijection _ _ (fun r => (pair (R1 r) (R2 r)))).
    + hnf; intros. inversion H0. destruct a1,a2. simpl in H2,H3.
      inversion H3. subst; auto.
    + hnf; intros. destruct b. exists (R n n0). simpl; auto. }
  apply bijection_injection in H,H0.
  assert (injection Rel nat). { apply (@injection_trans _ (nat * nat)); auto. }
  apply (@injection_Countable _ nat); auto. apply nat_Countable.
Qed.

Print term.

(* 定义公式的复杂度(逻辑深度) *)
Fixpoint term_complexity (t: term) : nat :=
  match t with
  | Tvar _ => 0
  | Tcon _ => 0
  | Tfun f => S (formula_complexity q)
  | Contain q r => S (max (formula_complexity q) (formula_complexity r))
  | ForAll _ q => S (formula_complexity q)
  end.


Lemma term_countable : Countable term.
Proof. 
  apply (@bijection_Countable _ nat); solve_Countable. apply bijection_sym.
  set (fun x => (Tcon (C x))) as f1.
  assert (function_injective f1). { hnf; intros. inversion H. auto. }
  set (fun x => (Tcon (C x))) as f2.
Admitted.

Lemma equality_countable : Countable (term -> term -> Formula).
Proof.
Admitted.

Lemma atomic_countable : Countable (forall r, Vector.t term (arity_R r) -> Formula).
Admitted.


Print Formula.

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

Lemma formula_complexity_countable : forall n,
  Countable (sig (fun x: Formula => formula_complexity x <= n)).
Proof.
  induction n.
  - apply (@bijection_Countable _ nat); solve_Countable. apply bijection_sym.
    set (s := sig (fun x => formula_complexity x <= 0)).
    pose proof @Bernstein_Theorem nat s. assert (Countable s). { admit. } 
    destruct X.
    set (x1 m := (equality (Tvar (X m)) (Tvar (X m)))).
    assert (forall m, formula_complexity (x1 m) <= 0). { simpl. lia. }
    set (s1 m := @exist Formula (fun x => formula_complexity x <= 0) (x1 m) (H0 m)).
    assert (@function_injective nat s (fun (n : nat) => s1 n)).
    { hnf; intros. inversion H1; auto. }
    apply (H _ _ H1 in_inj). constructor. exact (s1 0).
    (* apply (Build_bijection _ _ (fun x =>
      exist (fun x => formula_complexity x <= 0) (equality _ _) (le_n 0))).
    + hnf; intros. inversion H; auto.
    + hnf; intros. destruct b. inversion l. destruct x; inversion H0.
      exists n. f_equal. apply proof_irrelevance. *)
  - set (s := sig (fun x => formula_complexity x <= n)).
    apply (@injection_Countable _ (nat + s + s * s)%type); [| solve_Countable].
    (* assert (SNot : forall y m, formula_complexity (Not y) <= S m -> formula_complexity y <= m).
    { intros. simpl in H. lia. }
    assert (SContainl : forall m a b, formula_complexity (Contain a b) <= S m -> formula_complexity a <= m).
    { intros. simpl in H. lia. }
    assert (SContainr : forall m a b, formula_complexity (Contain a b) <= S m -> formula_complexity b <= m).
    { intros. simpl in H. lia. } *)
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
      exact (@inl (nat + s) (s * s) (@inl nat s 0)). } Admitted.

(*     apply (Build_bijection _ _ (fun x =>
      exist (fun x => formula_complexity x <= 0) (X x) (le_n 0))).
    + hnf; intros. inversion H; auto.
    + hnf; intros. destruct b. inversion l. destruct x; inversion H0.
      exists n. f_equal. apply proof_irrelevance.
  - set (s := sig (fun x => rankF x <= n)).
    apply (@injection_Countable _ (nat + s + s * s)%type); [| solve_Countable].
    assert (SNot : forall y m, rankF (Not y) <= S m -> rankF y <= m).
    { intros. simpl in H. lia. }
    assert (SContainl : forall m a b, rankF (Contain a b) <= S m -> rankF a <= m).
    { intros. simpl in H. lia. }
    assert (SContainr : forall m a b, rankF (Contain a b) <= S m -> rankF b <= m).
    { intros. simpl in H. lia. }
    apply (Build_injection _ _ (fun x => match x with
          | exist _ (X p) _ => inl (inl p)
          | exist _ (Not y) l => inl (inr (exist _ y (SNot _ _ l) ))
          | exist _ (Contain a b) l => inr (exist _ a (SContainl _ _ _ l),
            exist _ b (SContainr _ _ _ l)) end)).
    hnf; intros. destruct a1 as [[p1 | y1 | y1 z1] ?H];
    destruct a2 as [[p2 | y2 | y2 z2] ?H]; try inversion H.
    + f_equal. apply proof_irrelevance.
    + subst. f_equal. apply proof_irrelevance.
    + subst. f_equal. apply proof_irrelevance.
Qed. *)

(* Formula是可数的. *)
Theorem Formula_contable : Countable Formula.
Proof.
  apply (@injection_Countable _ (sigT (fun n => sig (fun x => formula_complexity x <= n)))).
  - apply (Build_injection _ _ 
    (fun x0 => existT (fun n => sig (fun x => formula_complexity x <= n)) (formula_complexity x0)
    (exist (fun x => formula_complexity x <= formula_complexity x0) x0 (le_n (formula_complexity x0))))).
    hnf; intros. inversion H. auto.
  - solve_Countable. apply formula_complexity_countable.
Qed.

(* 自然数和公式存在一一对应. *)
Lemma bijection_nat_formula : bijection nat Formula.
Proof.
  pose proof @Bernstein_Theorem nat Formula. pose proof Formula_contable. 
  destruct X. admit. Admitted.

(*  assert (@function_injective nat Formula (fun n => (X n))).
    { hnf; intros. inversion H0; auto. }
  apply (H _ _ H0 in_inj). constructor. exact (X 0).
Qed. *)

Theorem bij_NF : bijection nat Formula.
Proof. apply bijection_nat_formula. Qed.




(* 元数(arity)函数' *)
Definition arity_F' (f : Fun) : nat :=
  match f with
  | F a b => b
  end.


(* Require Import PeanoNat.
 *)
Definition cantor_pair (m n : nat) : nat := (m + n) * (m + n + 1) / 2 + m.

Lemma helper_le : forall s m, 
  m <= s -> (s * (s + 1)) / 2 + m < (s + 1) * (s + 2) / 2.
Proof. Admitted.
(* intros s m H.
rewrite <- Nat.add_sub_assoc by omega.
rewrite Nat.mul_add_distr_l.
simpl; omega.
Qed. *)

Theorem cantor_pair_inj : forall m1 n1 m2 n2,
  cantor_pair m1 n1 = cantor_pair m2 n2 -> m1 = m2 /\ n1 = n2.
Proof.
intros m1 n1 m2 n2 H.
(* let s1 := fresh "s" in let s2 := fresh "s" in
set (s1 := m1 + n1) in H; set (s2 := m2 + n2) in H. *)
unfold cantor_pair in H.

set (s1 := m1 + n1). set (s2 := m2 + n2).

Check Nat.compare_spec.

(* 分情况讨论 s1 与 s2 的大小关系 *)
(* case Nat.compare_spec s1 s2. *)
destruct (classicT (s1 = s2)). Admitted.
(* - (* 情况1：s1 = s2 *)
  intros Hed.
  rewrite Heq in H.
  assert (m1 = m2) as Hm by omega.
  split; [exact Hm |].
  rewrite Hm in Heq.
  rewrite Nat.add_comm in Heq; rewrite Nat.add_comm in s1.
  apply Nat.add_right_cancel in Heq; exact Heq.
- (* 情况2：s1 < s2 *)
  intros Hlt.
  assert (m1 <= s1) by omega.
  apply helper_le in Hlt.
  rewrite Nat.compare_lt_iff in Hlt.
  rewrite H in Hlt.
  assert (m2 <= s2) by omega.
  apply helper_le in Hlt.
  rewrite Nat.compare_lt_iff in Hlt.
  omega.
- (* 情况3：s1 > s2 *)
  intros Hgt.
  assert (m2 <= s2) by omega.
  apply helper_le in Hgt.
  rewrite Nat.compare_gt_iff in Hgt.
  rewrite H in Hgt.
  assert (m1 <= s1) by omega.
  apply helper_le in Hgt.
  rewrite Nat.compare_gt_iff in Hgt.
  omega.
Qed.
 *)

(* Fact eqF : forall (f g: Fun), 
  (arity_F f) = (arity_F g) /\  (arity_F' f) = (arity_F' g) -> f = g.
Proof.
  intros. destruct H. apply NNPP. intro. Admitted. *)

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

Fact Fun_countable : Countable Fun.
Proof.
  apply (@bijection_Countable _ nat); solve_Countable. apply bijection_sym.
  set (fun x => (F x x)) as f1.
  assert (function_injective f1). { hnf; intros. inversion H. auto. }
  set (fun F => (cantor_pair (arity_F F) (arity_F' F))) as f2. 
  assert (function_injective f2). 
    { hnf; intros. unfold f2 in H0. pose proof 
       (cantor_pair_inj (arity_F a1) (arity_F' a1) (arity_F a2) (arity_F' a2)).
      apply H1 in H0. 

 admit. }
  pose proof @ Bernstein_Theorem nat Fun. 
  pose proof H1 f1 f2 H H0. apply H2. constructor. exact (F 0 0).
Admitted.

(* 元数(arity)谓词' *)
Definition arity_R' (r : Rel) : nat :=
  match r with
  | R a b => b
  end.

Lemma Rel_countable : Countable Rel.
Proof.
  apply (@bijection_Countable _ nat); solve_Countable. apply bijection_sym.
  set (fun x => (R x x)) as f1.
  assert (function_injective f1). { hnf; intros. inversion H. auto. }
  set (fun R => (arity_R R) + ((arity_R R) + (arity_R' R))^2) as f2. 
  assert (function_injective f2). { hnf; intros. admit. }
  pose proof @ Bernstein_Theorem nat Rel. 
  pose proof H1 f1 f2 H H0. apply H2. constructor. exact (R 0 0).
Admitted.

Print term.

Lemma term_countable : Countable term.
Proof. 
  apply (@bijection_Countable _ nat); solve_Countable. apply bijection_sym.
  set (fun x => (Tcon (C x))) as f1.
  assert (function_injective f1). { hnf; intros. inversion H. auto. }
  set (fun x => (Tcon (C x))) as f2
Admitted.

Lemma equality_countable : Countable (term -> term -> Formula).
Proof.
Admitted.

Lemma atomic_countable : Countable (forall r, Vector.t term (arity_R r) -> Formula).
Admitted.

Print Formula.

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
Lemma formula_complexity_countable : forall n,
  Countable (sig (fun x: Formula => formula_complexity x <= n)).
Proof.
  induction n.
  - apply (@bijection_Countable _ nat); solve_Countable. apply bijection_sym.
    set (s := sig (fun x => formula_complexity x <= 0)).
    pose proof @Bernstein_Theorem nat s. assert (Countable s). { admit. } 
    destruct X.
    set (x1 m := (equality (Tvar (X m)) (Tvar (X m)))).
    assert (forall m, formula_complexity (x1 m) <= 0). { simpl. lia. }
    set (s1 m := @exist Formula (fun x => formula_complexity x <= 0) (x1 m) (H0 m)).
    assert (@function_injective nat s (fun (n : nat) => s1 n)).
    { hnf; intros. inversion H1; auto. }
    apply (H _ _ H1 in_inj). constructor. exact (s1 0).
    (* apply (Build_bijection _ _ (fun x =>
      exist (fun x => formula_complexity x <= 0) (equality _ _) (le_n 0))).
    + hnf; intros. inversion H; auto.
    + hnf; intros. destruct b. inversion l. destruct x; inversion H0.
      exists n. f_equal. apply proof_irrelevance. *)
  - set (s := sig (fun x => formula_complexity x <= n)).
    apply (@injection_Countable _ (nat + s + s * s)%type); [| solve_Countable].
    (* assert (SNot : forall y m, formula_complexity (Not y) <= S m -> formula_complexity y <= m).
    { intros. simpl in H. lia. }
    assert (SContainl : forall m a b, formula_complexity (Contain a b) <= S m -> formula_complexity a <= m).
    { intros. simpl in H. lia. }
    assert (SContainr : forall m a b, formula_complexity (Contain a b) <= S m -> formula_complexity b <= m).
    { intros. simpl in H. lia. } *)
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
      exact (@inl (nat + s) (s * s) (@inl nat s 0)). } Admitted.

(*     apply (Build_bijection _ _ (fun x =>
      exist (fun x => formula_complexity x <= 0) (X x) (le_n 0))).
    + hnf; intros. inversion H; auto.
    + hnf; intros. destruct b. inversion l. destruct x; inversion H0.
      exists n. f_equal. apply proof_irrelevance.
  - set (s := sig (fun x => rankF x <= n)).
    apply (@injection_Countable _ (nat + s + s * s)%type); [| solve_Countable].
    assert (SNot : forall y m, rankF (Not y) <= S m -> rankF y <= m).
    { intros. simpl in H. lia. }
    assert (SContainl : forall m a b, rankF (Contain a b) <= S m -> rankF a <= m).
    { intros. simpl in H. lia. }
    assert (SContainr : forall m a b, rankF (Contain a b) <= S m -> rankF b <= m).
    { intros. simpl in H. lia. }
    apply (Build_injection _ _ (fun x => match x with
          | exist _ (X p) _ => inl (inl p)
          | exist _ (Not y) l => inl (inr (exist _ y (SNot _ _ l) ))
          | exist _ (Contain a b) l => inr (exist _ a (SContainl _ _ _ l),
            exist _ b (SContainr _ _ _ l)) end)).
    hnf; intros. destruct a1 as [[p1 | y1 | y1 z1] ?H];
    destruct a2 as [[p2 | y2 | y2 z2] ?H]; try inversion H.
    + f_equal. apply proof_irrelevance.
    + subst. f_equal. apply proof_irrelevance.
    + subst. f_equal. apply proof_irrelevance.
Qed. *)

(* Formula是可数的. *)
Theorem Formula_contable : Countable Formula.
Proof.
  apply (@injection_Countable _ (sigT (fun n => sig (fun x => formula_complexity x <= n)))).
  - apply (Build_injection _ _ 
    (fun x0 => existT (fun n => sig (fun x => formula_complexity x <= n)) (formula_complexity x0)
    (exist (fun x => formula_complexity x <= formula_complexity x0) x0 (le_n (formula_complexity x0))))).
    hnf; intros. inversion H. auto.
  - solve_Countable. apply formula_complexity_countable.
Qed.

(* 自然数和公式存在一一对应. *)
Lemma bijection_nat_formula : bijection nat Formula.
Proof.
  pose proof @Bernstein_Theorem nat Formula. pose proof Formula_contable. 
  destruct X. admit. Admitted.

(*  assert (@function_injective nat Formula (fun n => (X n))).
    { hnf; intros. inversion H0; auto. }
  apply (H _ _ H0 in_inj). constructor. exact (X 0).
Qed. *)

Theorem bij_NF : bijection nat Formula.
Proof. apply bijection_nat_formula. Qed.

