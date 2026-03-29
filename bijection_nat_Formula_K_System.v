(**************************************************************************)
(*  This is part of bijection, it is distributed under the terms of the   *)
(*            GNU Lesser General Public License version 3                 *)
(*               (see file LICENSE for more details)                      *)
(*                                                                        *)
(*                       Copyright 2023-2028                              *)
(*         Dakai Guo, qiming Wang, jianghao Liu and Wensheng Yu           *)
(**************************************************************************)

(** bijection_nat_Formula_K_System *)

Require Import Mappings.
Require Import base_pc.
(* Require Import formulas_K_System. *)
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

(* (* 定义公式的复杂度(逻辑深度) *)
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


(* 公式集可数 *)
(* 对于任意自然数n, 层数小于等于n的公式的全体是可数的. *)
Fixpoint rankF (p:Formula): nat :=
  match p with
  | X _ => 0
  | Not x => 1 + rankF x
  | Contain x y => 1 + rankF x + rankF y
  end.

(* 对于任意自然数n, 层数小于等于n的公式的全体是可数的 *)
Lemma rankF_countable : forall n,
  Countable (sig (fun x: Formula => rankF x <= n)).
Proof.
  induction n.
  - apply (@bijection_Countable _ nat); solve_Countable. apply bijection_sym.
    apply (Build_bijection _ _ (fun x =>
      exist (fun x => rankF x <= 0) (X x) (le_n 0))).
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
Qed.

(* Formula是可数的. *)
Theorem Formula_contable : Countable Formula.
Proof.
  apply (@injection_Countable _ (sigT (fun n => sig (fun x => rankF x <= n)))).
  - apply (Build_injection _ _ 
    (fun x0 => existT (fun n => sig (fun x => rankF x <= n)) (rankF x0)
    (exist (fun x => rankF x <= rankF x0) x0 (le_n (rankF x0))))).
    hnf; intros. inversion H. auto.
  - solve_Countable. apply rankF_countable.
Qed.

(* 自然数和公式存在一一对应. *)
Lemma bijection_nat_formula : bijection nat Formula.
Proof.
  pose proof @Bernstein_Theorem nat Formula. pose proof Formula_contable. 
  destruct X. assert (@function_injective nat Formula (fun n => (X n))).
    { hnf; intros. inversion H0; auto. }
  apply (H _ _ H0 in_inj). constructor. exact (X 0).
Qed.

 *)