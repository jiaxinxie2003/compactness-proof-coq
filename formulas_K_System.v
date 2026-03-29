(**************************************************************************)
(*  This is part of formulas_pc, it is distributed under the terms of the *)
(*            GNU Lesser General Public License version 3                 *)
(*               (see file LICENSE for more details)                      *)
(*                                                                        *)
(*                       Copyright 2023-2028                              *)
(*         Dakai Guo, qiming Wang, jianghao Liu and Wensheng Yu           *)
(**************************************************************************)

(** formulas_K_System *)

Require Import base_pc.
(* Require Export Coq.Bool.Bool.*)
Require Export Coq.Arith.Arith.
(* Require Import Coq.Sets.Ensembles.*)
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Epsilon.
(*Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Relations.Relation_Definitions. *)
Require Import Coq.Vectors.Vector. 
Import VectorNotations.


(* 一阶语言符号 *)
(* 个体变元 *)
Inductive Var : Set :=
  | X : nat -> Var.

(* Variable Var : Type. *)

(* 个体常元 *)
Inductive Con : Set :=
  | C : nat -> Con.

(* 运算(函数)符 *)
Inductive Fun : Set :=
  | F : nat -> nat -> Fun.

(* 谓词 *)
Inductive Rel : Set :=
  | R : nat -> nat -> Rel.

(* 变元相关性质 *)
Definition var_num (v: Var): nat:=
  match v with
  | X n => n
  end.

Definition eqbv (n m: Var) : bool :=
  match n, m with
  | X p, X q => p =? q
  end.

(* 常元相关性质 *)
Definition con_num (v: Con): nat:=
  match v with
  | C n => n
  end.

Definition eqbc (n m: Con) : bool :=
  match n, m with
  | C p, C q => p =? q
  end.

(* 元数(arity)函数 *)
Definition arity_F (f : Fun) : nat :=
  match f with
  | F a b => S a
  end.

(* 元数(arity)谓词 *)
Definition arity_R (r : Rel) : nat :=
  match r with
  | R a b => S a
  end.

(* 项 *)
Inductive term : Set :=
  | Tvar : Var -> term
  | Tcon : Con -> term
  | Tfun : forall f: Fun, Vector.t term (arity_F f) -> term.

Print Vector.t.
(* Inductive t (A : Type) : nat -> Type :=
       nil : t A 0 | cons : A -> forall n : nat, t A n -> t A (S n) *)

(* 公式 *)
Inductive Formula :=
  | equality : term -> term -> Formula
  | atomic : forall (r: Rel), Vector.t (term) (arity_R r) -> Formula
  | Not : Formula -> Formula
  | Contain : Formula -> Formula -> Formula 
  | ForAll : Var -> Formula -> Formula.

Notation "t1 ≃ t2" := (equality t1 t2)(at level 5, right associativity).
Notation "¬ q" := (Not q)(at level 5, right associativity).
Notation "p → q" := (Contain p q)(at level 11, right associativity).
Notation "∀ x , p" := (ForAll x p) (at level 7, right associativity).

Definition Φ := @ Empty_set Formula.

Ltac ES := 
  match goal with
  | H: ?a ∈ Φ |- _ => destruct H
  | H: ?p0 ∈ [?p] |- _ => apply Single in H; rewrite H in *; ES
  | H: ?a ∈ (?B ∪ ?C) |- _ => apply UnionI in H; ES
  | |- ?a ∈ (?B ∪ ?C) => apply UnionI; ES
  | H: ?B \/ ?C |- _ => destruct H; ES
  | H: ?B /\ ?C |- _ => destruct H; ES
  | |- forall a, ?Q => intros; ES
  | |- ?P <-> ?Q => split; intros; ES
  | |- _ => eauto with sets
  end.

(* 其他符号 *)
Definition Inequality t1 t2 := Not (equality t1 t2). 

Definition Disjunction p q := Contain (Not p) q.

Definition Conjunction p q := Not (Contain p (Not q)).

Definition Equivalent p q := Conjunction (Contain p q) (Contain q p).

Definition Exists x p := Not (ForAll x (Not p)).

Notation " t1 ≄ t2 " := (Inequality t1 t2) (at level 4, right associativity).
Notation " p ∨ q " := (Disjunction p q) (at level 11, right associativity).
Notation " p ∧ q " := (Conjunction p q) (at level 9, right associativity).
Notation " p ↔ q " := (Equivalent p q) (at level 12, right associativity).
Notation "∃ x , p" := (Exists x p) (at level 8, right associativity).

(* 单点集记号 *)
Notation "[/ a ]" := (Singleton _ a) (at level 0, right associativity).
(* 两个集合之差 *)
Notation "A ~ B" := (Setminus _ A B) (at level 0, right associativity).

(* 变量集为空 *)
Definition Φ_Vr := @ Empty_set Var.

(* 常元集为空 *)
Definition Φ_Co := @ Empty_set Con.

(* 项的变元集T_Vr; 项中无量词, 项中的变元都是自由的, 故该变元集也是自由变元集 *)
Fixpoint term_Ens (t: term) :=
  match t with
  | Tcon c => Φ_Vr
  | Tvar x => [/x]
  | Tfun  _ q => let fix Vector_Ens (n: nat) (r: Vector.t (term) n) :=
                   match r with 
                   | nil _ => Φ_Vr
                   | cons _ h _ q => (term_Ens h) ∪ (Vector_Ens _ q)
                   end in Vector_Ens _ q
  end. 

(* 项向量的变元集TV_Vr; 该变元集也是自由变元集 *)
Fixpoint Vector_Ens (n: nat) (r: Vector.t (term) n) :=
  match r with 
  | nil _ => Φ_Vr
  | cons _ h _ q => (term_Ens h) ∪ (Vector_Ens _ q)
  end.

(* 公式的变元集F_Vr *)
Fixpoint Formula_Ens (p: Formula) :=
  match p with 
  | equality t1 t2 => (term_Ens t1) ∪ (term_Ens t2)
  | atomic _ q => Vector_Ens _ q
  | Not q => Formula_Ens q
  | Contain m n =>  (Formula_Ens m) ∪ (Formula_Ens n)
  | ForAll x q => (Formula_Ens q) ∪ [/x]
  end.

(* 项的常元集T_C_set *)
Fixpoint term_C_set (t: term) :=
  match t with
  | Tcon c => [/c]
  | Tvar x => Φ_Co
  | Tfun  _ q => let fix Vector_C_set (n: nat) (r: Vector.t (term) n) :=
                   match r with 
                   | nil _ => Φ_Co 
                   | cons _ h _ q => (term_C_set h) ∪  (Vector_C_set _ q)
                   end in Vector_C_set _ q
  end.

(* 项向量的常元集TV_C_set *)
Fixpoint Vector_C_set (n: nat) (r: Vector.t (term) n) :=
  match r with 
  | nil _ => Φ_Co
  | cons _ h _ q => (term_C_set h) ∪ (Vector_C_set _ q)
  end.

(* 公式的常元集F_C_set *)
Fixpoint Formula_C_set (p: Formula) :=
  match p with 
  | equality t1 t2 => (term_C_set t1) ∪ (term_C_set t2)
  | atomic _ q => Vector_C_set _ q
  | Not q => Formula_C_set q
  | Contain m n =>  (Formula_C_set m) ∪ (Formula_C_set n)
  | ForAll x q => (Formula_C_set q) 
  end.

(* 公式的自由变元集 *)
Fixpoint Formula_free_Ens (p: Formula) :=
  match p with 
  | equality t1 t2 => (term_Ens t1) ∪ (term_Ens t2)
  | atomic _ q => Vector_Ens _ q
  | Not q => Formula_free_Ens q
  | Contain m n => (Formula_free_Ens m) ∪ (Formula_free_Ens n)
  | ForAll x q => (Formula_free_Ens q) ~ [/x]
  end.

(* 公式的约束变元集 *)
Fixpoint Formula_bound_Ens (p: Formula) :=
  match p with 
  | equality t1 t2 => Φ_Vr
  | atomic _ q => Φ_Vr
  | Not q => Formula_bound_Ens q
  | Contain m n => (Formula_bound_Ens m) ∪ (Formula_bound_Ens n)
  | ForAll x q => (Formula_bound_Ens q) ∪ [/x]
  end.

(* 闭项: 只含个体常元的项叫做闭项 *)
Definition closed_term (t: term) := term_Ens t = Φ_Vr.
  
(* 语句(闭式): 不含自由变元的公式 *)
Definition statement (p: Formula) := Formula_free_Ens p = Φ_Vr.

(* 项的变元和常元组成的项子集 *)
Fixpoint ST (t: term) : Ensemble term :=
  match t with
  | Tcon c => [/t]
  | Tvar x => [/t]
  | Tfun  _ q => let fix Vector_ST (n: nat) (r: Vector.t (term) n) :=
                   match r with 
                   | nil _ => (@ Empty_set term)
                   | cons _ h _ q => (ST h) ∪ (Vector_ST _ q)
                   end in [/t] ∪ (Vector_ST _ q)
  end.
Check ST.
(* Goal forall t : term, (ST t) = (term_Ens t) ∪ (term_C_set t). *)

(* 项向量的仅由变元和常元组成的子项集 *)
Fixpoint Vector_ST (n: nat) (r: Vector.t (term) n) : Ensemble term :=
   match r with 
   | nil _ => (@ Empty_set term)
   | cons _ h _ q => (ST h) ∪ (Vector_ST _ q)
   end.

(* 公式的仅由变元和常元组成的子项集 *)
Fixpoint Formula_ST (t: Formula) : Ensemble term :=
  match t with
  | equality a b => (ST a) ∪ (ST b)
  | atomic _ vr => (Vector_ST _ vr)
  | Not a => (Formula_ST a)
  | Contain a b => (Formula_ST a) ∪ (Formula_ST b)
  | ForAll x a => [/(Tvar x)] ∪ (Formula_ST a)
  end.

(* 对子项集封闭的项集 *)
Definition Closed_ST (ET : Ensemble term) := forall s, s ∈ ET -> (ST s) ⊆ ET.

(* 公式的子公式集 *)
Fixpoint Formula_SF (s: Formula) : Ensemble Formula :=
  match s with
  | equality a b => [/s]
  | atomic _ _ => [/s]
  | Not a => [/s] ∪ (Formula_SF a)
  | Contain a b => [/s] ∪ (Formula_SF a) ∪ (Formula_SF b)
  | ForAll x a => [/s] ∪ (Formula_SF a)
  end.

(* 对子公式封闭的公式集 *)
Definition Closed_SF (S: Ensemble Formula) := forall s, s ∈ S 
  -> (Formula_SF s) ⊆ S.

(* 加强版排中律 *)
Theorem classicT : forall P, {P} + {~ P}.
Proof.
  intros. assert { x: bool | if x then P else ~ P }.
  { apply constructive_indefinite_description. destruct (classic P).
    - exists true. auto.
    - exists false. auto. }
  destruct H, x; auto.
Qed.

(* 项t对p中变元x是自由的 *)
Fixpoint t_x_free (p: Formula) (t: term) (x: Var) :=
  match p with 
  | equality t1 t2 => true
  | atomic _ q => true 
  | Not q => t_x_free q t x
  | Contain m n => andb (t_x_free m t x) (t_x_free n t x)
  | ForAll y q => match (classicT (x ∈ (Formula_free_Ens p))) with
                  | left _ => match (classicT (y ∈ (term_Ens t))) with
                              | left _ => false
                              | right _ => t_x_free q t x
                              end
                  | right _ => true
                  end
  end.

(* t是闭项, 则t对公式p中的x是自由的 *)
Fact free_test_1: forall x p t, closed_term t -> t_x_free p t x = true.
Proof.
  intros. induction p.
  - simpl. auto.
  - simpl. auto.
  - simpl. apply IHp.
  - simpl. rewrite IHp1,IHp2. auto.
  - simpl. destruct (classicT (x ∈ (Formula_free_Ens p) ~ [/v])).
    destruct (classicT (v ∈ (term_Ens t))).
    + rewrite H in i0. elim i0.
    + auto.
    + auto.
Qed.

Fact union_complement_equiv: forall (A B: Ensemble Var) x,
  (~ x ∈ (A ∪ B)) <-> (~ x ∈ A) /\ (~ x ∈ B).
Proof.
  split; intro.
  - split; red; intro; destruct H; ES.
  - destruct H. red. intro. destruct H1; contradiction.
Qed.

Fact free_contain_Ens: forall (p: Formula), (Formula_free_Ens p) ⊆ (Formula_Ens p).
Proof.
  red. intros. induction p.
  - auto.
  - auto.
  - apply IHp. auto.
  - destruct H.
    + left. apply IHp1. auto.
    + right. apply IHp2. auto.
  - simpl in *. destruct H. ES.
Qed.

(* x不在公式中自由出现, 则t对公式p中的x是自由的 *)
Fact free_test_2: forall x p t, ~ (x ∈ (Formula_Ens p)) -> t_x_free p t x = true.
Proof.
  intros; induction p; simpl.
  - auto.
  - auto.
  - apply IHp. apply H.
  - apply union_complement_equiv in H. destruct H.
    rewrite IHp1,IHp2; eauto.
  - destruct (classicT (x ∈ (Formula_free_Ens p) ~ [/v])).
    destruct (classicT (v ∈ (term_Ens t))).
    + destruct i. apply union_complement_equiv in H as [H _].
      elim H. apply free_contain_Ens. auto.
    + apply IHp. apply union_complement_equiv in H as []. auto.
    + auto.
Qed.

(* 项x对公式p中的x是自由的 *)
Fact free_test_3: forall x p, t_x_free p (Tvar x) x = true.
Proof.
  intros; induction p; simpl.
  - auto.
  - auto.
  - auto.
  - rewrite IHp1,IHp2. auto.
  - destruct (classicT (x ∈ (Formula_free_Ens p) ~ [/v])).
    destruct (classicT (v ∈ [/x])). destruct i0. destruct i.
    elim H0. apply In_singleton. auto. auto.
Qed.

(* 在项t中把变元x替换成t': t(x;t') *)
Fixpoint substitute_t (t t': term) (x: Var) :=
  match t with
  | Tcon c => Tcon c
  | Tvar y => if (eqbv x y) then t' else Tvar y 
  | Tfun  _ q => let fix substitute_v (n: nat) (r: Vector.t (term) n)
                   (t': term) (x: Var) :=
                   match r with 
                   | [] => []
                   | h :: q => (substitute_t h t' x) :: (substitute_v _ q t' x) 
                   end in (Tfun _ (substitute_v _ q t' x))
  end.
Notation " r { x ; s } ":= (substitute_t r s x)(at level 0).

(* 在项t中把常元x替换成t': tc(x;t') *)
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
  end.

(* 向量项替换 *)
Fixpoint substitute_v (n: nat) (r: Vector.t term n) 
  (t': term) (x: Var) :=
  match r with 
  | [] => []
  | h :: q => (substitute_t h t' x) :: (substitute_v _ q t' x)
  end.

(* 公式p中把变元x替换成t' *)
Fixpoint substitute_f (p: Formula) (t': term) (x: Var) :=
  match p with 
  | equality t1 t2 => equality (substitute_t t1 t' x) (substitute_t t2 t' x) 
  | atomic _ q => atomic _ (substitute_v _ q t' x) 
  | Not q => Not (substitute_f q t' x)
  | Contain m n => Contain (substitute_f m t' x) (substitute_f n t' x)
  | ForAll y q => if (eqbv x y) then ForAll y q
                    else ForAll y (substitute_f q t' x)
  end.
Notation " p { x ;; r } ":= (substitute_f p r x)(at level 0).

Fixpoint equality_4 
  (r: Formula) (m n: nat) (v1: Vector.t term m) (v2: Vector.t term n) :=
    match v1 with
    | nil _ => r
    | cons _ h _ s => match v2 with
                      | nil _ => r
                      | cons _ l _ t => (equality h l) → (equality_4 r _ _ s t)
                      end
    end.


(* 归纳证明 *)
(* 项的归纳函数 *)
Section term_ind_process.
Variable P : term -> Prop.
Variable P0 : forall n, Vector.t term n -> Prop.
Variable varcase : forall n, P (Tvar n).
Variable concase : forall n, P (Tcon n).
Variable nilcase : forall s, P0 0 s.
Variable applycase : forall (f: Fun) (v: t term (arity_F f)), 
  P0 (arity_F f) v -> P (Tfun _ v).
Variable conscase : forall n (s: term) (t0: Vector.t term n),
  P s -> P0 n t0 -> P0 (S n) (s :: t0).
Fixpoint Term_ind_new (s: term) : P s :=
  let fix Terms_ind n (vec: (Vector.t term n)) : P0 n vec :=
    match vec in (t _ n) return (P0 n vec) with
    | nil _ => nilcase (nil _)
    | cons _ t0 m ts =>
      conscase m t0 ts (Term_ind_new t0) (Terms_ind m ts)
    end in match s with
           | Tvar r => varcase r
           | Tcon r => concase r
           | Tfun f ts => applycase f ts (Terms_ind _ ts)
           end.
End term_ind_process.



