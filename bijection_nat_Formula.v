(**************************************************************************)
(*  This is part of bijection, it is distributed under the terms of the   *)
(*            GNU Lesser General Public License version 3                 *)
(*               (see file LICENSE for more details)                      *)
(*                                                                        *)
(*                       Copyright 2023-2028                              *)
(*         Dakai Guo, qiming Wang, jianghao Liu and Wensheng Yu           *)
(**************************************************************************)

(** bijection_nat_Formula1 *)

Require Import Mappings1.
Require Import base_pc.
Require Import formulas_K_System.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Epsilon.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.

Theorem classicT : forall (P: Prop), {P} + {~P}.
Proof.
  intros. assert {x:bool | if x then P else ~P}.
  { apply constructive_indefinite_description. destruct (classic P).
    - exists true. auto.
    - exists false. auto. }
  destruct H, x; auto.
Qed.


Section bernstein.

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


(**************************************************************************)
(* 项可数 *)
Print term.

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

(* 如果 A 是可数的，那么 A 的 n 维向量也是可数的 *)
Lemma Vec_countable : forall A n, Countable A -> Countable (Vector.t A n).
Proof.
  intros. induction n.
  - apply (@injection_Countable _ nat).
    + exists (fun _ => 0). hnf; intros.
      (* 证明 a1 = a2 = Vector.nil *)
      assert (a1 = Vector.nil A) by (apply (Vector.case0 (fun v => v = Vector.nil A)); auto).
      assert (a2 = Vector.nil A) by (apply (Vector.case0 (fun v => v = Vector.nil A)); auto).
      subst; auto.
    + apply nat_Countable.
  - (* Inductive Step: S n 维向量同构于 A * Vector A n *)
    apply (@bijection_Countable _ (A * Vector.t A n)).
    + apply (Build_bijection _ _ (fun v => (Vector.hd v, Vector.tl v))).
      -- hnf; intros.
        assert (a1 = Vector.cons A (Vector.hd a1) n (Vector.tl a1)) by (apply Vector.eta; auto).
        assert (a2 = Vector.cons A (Vector.hd a2) n (Vector.tl a2)) by (apply Vector.eta; auto).
        rewrite H0, H1. inversion H. subst. auto.
      -- hnf; intros. destruct b as [a v]. exists (Vector.cons A a n v). simpl. auto.
    + apply prod_Countable; auto.
Qed.
(* Vector.case0：这是一个针对 0 维向量的分类讨论工具。它证明了“如果向量长度为 0，那么它必然等于 Vector.nil”。
   Vector.hd 和 Vector.tl：分别获取向量的头部（第一个元素）和尾部（剩余部分）。
   Vector.eta：向量的“外延性”定理，即：任何非空向量 v 都等于 cons (hd v) (tl v)。
   bijection_Countable：这是一个引理，意思是通过证明 X 与已知可数类型 Y 之间存在双射，来证明 X 可数。 *)

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

(* 定义项的秩(复杂度) *)
Fixpoint term_rank (t : term) : nat :=
  match t with
  | Tvar _ => 0
  | Tcon _ => 0
  | Tfun _ q => let fix term_vec_rank (n:nat) (v : Vector.t term n) :=
                match v with
                | Vector.nil _ => 0
                | Vector.cons _ t _ ts => max (term_rank t) (term_vec_rank _ ts)
                end in S (term_vec_rank _ q)
end.

Lemma Trank_countable_lemma1 :
  Countable (sig (fun t : term => term_rank t <= 0)).
Proof.
  apply (@injection_Countable _ (Var + Con)).
  - apply (Build_injection _ _
    (fun x => match x with
      | exist _ (Tvar v) _ => inl v
      | exist _ (Tcon c) _ => inr c
      | exist _ (Tfun f q) Hrank => 
          (* 因为 Tfun 的 rank 是 S (...)，矛盾于 Hrank : rank <= 0 *)
          False_rect (Var + Con) (Nat.nle_succ_0 _ Hrank)
      end)).
    hnf; intros [t1 p1] [t2 p2] Heq.
    (* 分类讨论项的结构 *)
    destruct t1; destruct t2;
    try (inversion Heq; subst; f_equal; try apply proof_irrelevance);
    try (simpl in *; lia).
  - solve_Countable. apply Var_countable. apply Con_countable.
Qed.

(* 引理：如果函数项的秩 <= S n，那么其向量中每个元素的秩 <= n *)
Lemma Tfun_rank_to_vec_inv : forall f v n,
  term_rank (Tfun f v) <= S n -> (forall t, Vector.In t v -> term_rank t <= n).
Proof.
  simpl. intros. induction H0; try apply IHIn; lia.
Qed.

(* 将一个普通的项向量（Vector.t term k）转换成
   “带证明的项”向量（Vector.t {t : term | term_rank t <= n} k） *)
Fixpoint v_sig_map {n k} (v : Vector.t term k) :
  (forall t, Vector.In t v -> term_rank t <= n) -> Vector.t ({t | term_rank t <= n}) k :=
  match v with
  | Vector.nil _ => fun _ => Vector.nil _
  | Vector.cons _ h _ ts => fun H =>
      Vector.cons _ (exist _ h (H h (@Vector.In_cons_hd term _ _ _)))
                  _ (v_sig_map ts (fun t Hin => H t (@Vector.In_cons_tl term _ _ _ _ Hin)))
  end.

Lemma v_sig_map_injective : forall (n k : nat) (v1 v2 : Vector.t term k) H1 H2,
  @v_sig_map n k v1 H1 = @v_sig_map n k v2 H2 -> v1 = v2.
Proof.
  intros n k v1. induction v1; intros v2 H1 H2 Heq.
  - assert (v2 = Vector.nil term)
      by (apply (Vector.case0 (fun v => v = Vector.nil term)); auto).
    subst; reflexivity.
  - dependent destruction v2. simpl in Heq. inversion Heq.
    subst h0. f_equal.
    apply IHv1 with (H1 := (fun t Hin => H1 t (Vector.In_cons_tl t h v1 Hin)))
                    (H2 := (fun t Hin => H2 t (Vector.In_cons_tl t h v2 Hin))).
    dependent destruction H3. auto.
Qed.

(* 在 Coq 的标准库中，{x : A & P x} 是类型 sigT (fun x : A => P x) 的语法糖 *)
Lemma Trank_countable_lemma2 : forall n,
  Countable ({t: term | term_rank t <= n}).
Proof.
  induction n.
  - apply Trank_countable_lemma1.
  - set (Cn := {t : term | term_rank t <= n}). red.
    (* T_{n+1} 可以单射到 Var + Con + {f : Fun & Vector.t Cn (arity_F f)} *)
    apply (@injection_Countable _ (Var + Con + {f : Fun & Vector.t Cn (arity_F f)})).
    + (* 构造单射函数，将 Tfun f args 映射到 sigT 部分 *)
     apply (Build_injection _ _
     (fun x => match x with
        | exist _ (Tvar v) _ => inl (inl v)
        | exist _ (Tcon c) _ => inl (inr c)
        | exist _ (Tfun f v) Hf => 
            let Hinv := Tfun_rank_to_vec_inv f v n Hf in
            inr (existT _ f (v_sig_map v Hinv))
        end)).
      (* 证明单射性 *)
      hnf; intros [t1 p1] [t2 p2] Heq.
      destruct t1; destruct t2; inversion Heq; subst; f_equal; try apply proof_irrelevance.
      dependent destruction H1. apply v_sig_map_injective in x.
      subst t0. f_equal. apply proof_irrelevance.
    + solve_Countable. apply Var_countable. apply Con_countable.
      apply Fun_countable. apply Vec_countable. auto.
Qed.

(* Term是可数的 *)
Theorem Term_countable : Countable term.
Proof.
  apply (@injection_Countable _ ({n : nat & {t : term | term_rank t <= n}})).
  - apply (Build_injection _ _ 
      (fun t => existT (fun n => {t : term | term_rank t <= n})
                       (term_rank t) (exist _ t (le_n (term_rank t))))).
    hnf; intros. inversion H. auto.
  - repeat solve_Countable. apply Trank_countable_lemma2.
Qed.

(**************************************************************************)
(* 公式可数 *)
Print Formula.

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

(* 定义公式的复杂度(逻辑深度) *)
Fixpoint formula_rank (p: Formula) : nat :=
  match p with
  | equality _ _ => 0
  | atomic _ _ => 0
  | Not q => S (formula_rank q)
  | Contain q r => S (max (formula_rank q) (formula_rank r))
  | ForAll _ q => S (formula_rank q)
  end.

Lemma Formula_countable_lemma1 :
  Countable ({x : Formula | formula_rank x <= 0}).
Proof.
  apply (@injection_Countable _ (term * term + {r : Rel & Vector.t term (arity_R r)})).
  - apply (Build_injection _ _
      (fun x => match x with
        | exist _ (equality t1 t2) _ => inl (t1, t2)
        | exist _ (atomic r args) _ => inr (existT _ r args)
        | exist _ _ Hrank => False_rect _ (Nat.nle_succ_0 _ Hrank)
        end)).
    hnf; intros [f1 p1] [f2 p2] Heq.
    destruct f1; destruct f2;
    try (inversion Heq; subst; f_equal; try apply proof_irrelevance);
    try (simpl in *; lia).
  - pose proof Term_countable. solve_Countable.
    apply Rel_countable. apply Vec_countable. auto.
Qed.

Lemma rank_Sn_to_n_Not : forall q n, formula_rank (Not q) <= S n -> formula_rank q <= n.
Proof. simpl; intros; lia. Qed.
Lemma rank_Sn_to_n_Contain_l : forall q r n, formula_rank (Contain q r) <= S n -> formula_rank q <= n.
Proof. simpl; intros; lia. Qed.
Lemma rank_Sn_to_n_Contain_r : forall q r n, formula_rank (Contain q r) <= S n -> formula_rank r <= n.
Proof. simpl; intros; lia. Qed.
Lemma rank_Sn_to_n_ForAll : forall v q n, formula_rank (ForAll v q) <= S n -> formula_rank q <= n.
Proof. simpl; intros; lia. Qed.

Lemma Formula_countable_lemma2 : forall n,
  Countable ({x : Formula | formula_rank x <= n}).
Proof.
  induction n.
  - apply Formula_countable_lemma1.
  - set (C0 := {x : Formula | formula_rank x <= 0}).
    set (Cn := {x : Formula | formula_rank x <= n}).
    apply (@injection_Countable _ (C0 + (Cn + (Cn * Cn) + (Var * Cn)))).
    + apply (Build_injection _ _
      (fun x => match x with
        | exist _ (equality t1 t2) p =>
            inl (exist (fun x => formula_rank x <= 0) (equality t1 t2) (Nat.le_refl 0))
        | exist _ (atomic r args) p  =>
            inl (exist (fun x => formula_rank x <= 0) (atomic r args) (Nat.le_refl 0))
        | exist _ (Not q) Hr =>
            inr (inl (inl (exist _ q (rank_Sn_to_n_Not _ _ Hr))))
        | exist _ (Contain q r) Hr =>
            inr (inl (inr (exist _ q (rank_Sn_to_n_Contain_l _ _ _ Hr), 
                           exist _ r (rank_Sn_to_n_Contain_r _ _ _ Hr))))
        | exist _ (ForAll v q) Hr =>
            inr (inr (v, exist _ q (rank_Sn_to_n_ForAll _ _ _ Hr)))
        end)).
      (* 证明单射性 *)
      hnf; intros [f1 p1] [f2 p2] Heq.
      destruct f1; destruct f2; inversion Heq; subst; f_equal; try apply proof_irrelevance.
    + solve_Countable. apply Formula_countable_lemma1. apply Var_countable.
Qed.

(* Formula是可数的. *)
Theorem Formula_contable : Countable Formula.
Proof.
  apply (@injection_Countable _ ({n : nat & {x : Formula | formula_rank x <= n}})).
  - apply (Build_injection _ _ 
    (fun x0 => existT (fun n => sig (fun x => formula_rank x <= n)) (formula_rank x0)
    (exist (fun x => formula_rank x <= formula_rank x0) x0 (le_n (formula_rank x0))))).
    hnf; intros. inversion H. auto.
  - repeat solve_Countable. apply Formula_countable_lemma2.
Qed.

(* 自然数和公式存在一一对应. *)
Lemma bijection_nat_formula : bijection nat Formula.
Proof.
  pose proof @Bernstein_Theorem nat Formula. pose proof Formula_contable.
  destruct X as [g Hg].
  set (f := fun (n : nat) => equality (Tvar (X n)) (Tvar (X n))).
  assert (Hf : function_injective f). { red; intros. inversion H0. auto. } 
  apply (H f g); auto. constructor. exact (f 0).
Qed.

