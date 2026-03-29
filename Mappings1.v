(**************************************************************************)
(*   This is part of Mappings, it is distributed under the terms of the   *)
(*            GNU Lesser General Public License version 3                 *)
(*               (see file LICENSE for more details)                      *)
(*                                                                        *)
(*                       Copyright 2023-2028                              *)
(*         Dakai Guo, qiming Wang, jianghao Liu and Wensheng Yu           *)
(**************************************************************************)

(** Mappings *)

(*Require Import Coq.Logic.Classical.*)
Require Import Coq.Logic.Epsilon.
Require Import Coq.micromega.Lia.
(* Require Import Coq.Arith.Div2. *)

(* 单射函数 *) 
Definition function_injective {A B} (f: A -> B): Prop :=
  forall a1 a2, f a1 = f a2 -> a1 = a2.

(* 满射函数 *)
Definition function_surjective {A B} (f: A -> B): Prop := 
  forall b, exists a, f a = b.

(* 双射函数 *)
Inductive function_bijective {A B} (f: A -> B): Prop :=
  | fun_bij_intro : function_injective f -> function_surjective f 
                      -> function_bijective f.

(* 任意两个类型A、B的单射类型 *)
Record injection (A B: Type): Type := {
  inj_f:> A -> B;
  in_inj: function_injective inj_f }.
  
Check Build_injection.
(* Build_injection
     : forall (A B : Type) (inj_f : A -> B), function_injective inj_f -> injection A B *)

(* 满射类型 *)
Record surjection (A B: Type): Type := {
  sur_f:> A -> B;
  su_surj: function_surjective sur_f }.

(* 双射类型 *)
Record bijection (A B: Type): Type := {
  bij_f:> A -> B;
  in_bij: function_injective bij_f;
  su_bij: function_surjective bij_f }.

(* 若A单射B且B单射C, 则A单射C. *)
Definition injection_trans {A B C} (f1: injection A B) (f2: injection B C): 
  injection A C.
  apply (Build_injection _ _ (fun a => f2 (f1 a))). hnf; intros. 
  apply (in_inj _ _ f2) in H. apply (in_inj _ _ f1) in H. auto.
Defined.

(* 若A双射B, 则B双射A. *)
Definition bijection_sym {A B} (f: bijection A B): bijection B A.
  apply (Build_bijection _ _ (fun b => proj1_sig 
  (constructive_indefinite_description _ ((su_bij _ _ f) b)))).
  - hnf; intros. repeat destruct constructive_indefinite_description.
    simpl in H. congruence.
  - hnf; intros. exists (bij_f _ _ f b). 
    destruct constructive_indefinite_description.
    simpl. apply (in_bij _ _ f). auto.
Defined.

(* 若A1单射B1且A2单射B2, (A1+A2)单射(B1+B2). (此处+号代表和类型, 可理解为不相交的并) *)
Definition sum_injection {A1 B1 A2 B2} (f1: injection A1 B1) 
  (f2: injection A2 B2): injection (sum A1 A2) (sum B1 B2).
  apply (Build_injection _ _ (fun a =>
         match a with
         | inl x => inl (f1 x) 
         | inr y => inr (f2 y) end)).
  hnf; intros. destruct a1, a2; try inversion H.
  - inversion H. apply (in_inj _ _ f1) in H1. f_equal; auto.
  - inversion H. apply (in_inj _ _ _) in H1. f_equal; auto.
Defined.

(* 若A1单射B1且A2单射B2, 则(A1*A2)单射(B1*B2).(此处*号代表积类型, 可理解为笛卡尔积) *)
Definition prod_injection {A1 B1 A2 B2} (f1: injection A1 B1)
  (f2: injection A2 B2): injection (prod A1 A2) (prod B1 B2).
  apply (Build_injection _ _ (fun m =>
          match m with
          | (m1, m2) => (f1 m1, f2 m2) end )).
  hnf; intros. destruct a1, a2.
  inversion H. apply in_inj in H1. apply in_inj in H2. congruence.
Defined.

(* 若对任意I类型的项i, 都有A_i单射B, 那么(sigT A)单射(I*B).
(这个引理可理解为对于指标集I,若任意i∈I都存在一个A_i到B的单射, 
那么存在一个从⋃_(i=0)^∞ A_i 到I和B的笛卡尔积的单射) *)
Definition sigT_injection (I: Type) (A: I -> Type) (B: Type)
  (f: forall i: I, injection (A i) B): injection (sigT A) (I * B).
  apply (Build_injection _ _ (fun a => (projT1 a, f (projT1 a) (projT2 a)))).
  hnf; intros. inversion H. destruct a1,a2. simpl in *.
  subst. apply (in_inj _ _ (f x0)) in H2. congruence.
Defined.

(* A类型到B类型存在双射,那么可以构造A类型到B类型的单射. *)
Definition bijection_injection {A B} (f: bijection A B): injection A B :=
  Build_injection _ _ f (in_bij _ _ f).

(*  (nat+nat)双射nat.  *)
Definition nat2_nat_bijection: bijection (sum nat nat) nat.
  apply (Build_bijection _ _ (fun n =>
         match n with 
         | inl n => n + n 
         | inr n => S (n + n) end)).
  - hnf; intros. destruct a1 eqn:Ha1, a2 eqn:Ha2; try lia; f_equal; lia.
  - hnf; intros.
    assert (forall n, exists m, n= m + m \/ n = S (m + m)).
    { intros. induction n. eauto. destruct IHn. destruct H.
      - exists x; lia.
      - exists (S x); lia. }
    destruct (H b) as [n []].
    + exists (inl n). auto.
    + exists (inr n); auto.
Defined.

(* (nat*nat)双射nat. *)
Definition natnat_nat_bijection: bijection (prod nat nat) nat.
  set (fix sum (x : nat) : nat := match x with
       | 0 => 0
       | S x0 => S x0 + sum x0
       end) as f.
  apply (Build_bijection _ _
    (fun n => match n with | (n1, n2) => f (n1+n2) + n1 end)).
  - hnf; intros. destruct a1 as (a11, a12), a2 as (a21, a22).
    assert (forall m1 m2, m1 < m2 -> f m1 + m1 < f m2).
    { intros. remember (m2 - m1 - 1) as d;
      assert (m2 = (S d) + m1) by lia.
      subst m2. clear. induction d; simpl in *; lia. }
    destruct (Compare_dec.le_lt_dec (a11 + a12) (a21 + a22)).
    + destruct (Lt.le_lt_or_eq _ _ l).
      * pose proof H0 _ _ H1. lia.
      * rewrite H1 in *. assert (a11=a21) by lia. subst.
        assert (a12 = a22) by lia. auto.
    + apply H0 in l. lia.
  - hnf; intros. assert ( forall a, exists s, f s <= a < f (S s)).            
    { induction a. exists 0. auto. destruct IHa as [s Hs].
      remember (a - f s) as d.
      destruct (PeanoNat.Nat.lt_ge_cases d s).
      + exists s. simpl in *. lia.
      + exists (S s). simpl in *; lia. }
    destruct (H b) as [s Hs]. remember (b - (f s)) as a1.
    assert (a1 <= s) by (unfold f in *; lia).
    exists (a1, s-a1). replace (a1 + (s - a1)) with s by lia. lia.
Defined.

Definition Countable (A: Type): Type := injection A nat.

(* 若A单射B且B可数, 则A可数.  *)
Definition injection_Countable {A B} (R: injection A B)
  (CB: Countable B): Countable A := injection_trans R CB.

(* 若A双射B且B可数, 则A可数.  *)
Definition bijection_Countable {A B} (R: bijection A B) (CB: Countable B): 
  Countable A := injection_Countable (bijection_injection R) CB.

(* 若A可数且B可数, 则(A+B)可数. *)
Definition sum_Countable {A B} (CA: Countable A) (CB: Countable B): 
  Countable (sum A B) :=injection_trans
  (sum_injection CA CB) (bijection_injection nat2_nat_bijection).

(* 若A可数且B可数, 则(A*B)可数. *)
Definition prod_Countable {A B} (CA: Countable A) (CB: Countable B): 
  Countable (prod A B) :=injection_trans 
  (prod_injection CA CB) (bijection_injection natnat_nat_bijection).

(* (* 若对所有自然数i, 均有A_i可数, 则(sigT A可数). *) 
Definition nCountable_Countable {A: nat -> Type} 
  (CA: forall n, Countable (A n)): Countable (sigT A) :=
  injection_trans (sigT_injection _ _ _ CA)
  (bijection_injection natnat_nat_bijection). *)

(* 自然数可数 *)
Definition nat_Countable : Countable nat.
  apply (Build_injection _ _ (fun n => n )). hnf; intros. eauto.
Defined.

(* sigT A：依赖对类型，等价于存在量词∃i: I, A i表示“存在i使得A i成立”的所有(i, a)对 *)
Definition sigT_Countable {I: Type} {A: I -> Type}
  (CI: Countable I) (CA: forall i, Countable (A i)): Countable (sigT A).
  (* 1. 利用 sigT_injection 将 sigT A 映射到 (I * nat) *)
  (* 注意：CA i 的类型就是 Countable (A i)，即 injection (A i) nat *)
  apply (injection_trans (sigT_injection I A nat CA)).
  (* 2. 证明 (I * nat) 是可数的 *)
  apply prod_Countable. apply CI. apply nat_Countable.
Defined.

Ltac solve_Countable :=
  match goal with
  | |- Countable (sum _ _) => apply sum_Countable; solve_Countable
  | |- Countable (prod _ _) => apply prod_Countable; solve_Countable
  | |- Countable (sigT _) => apply sigT_Countable; try intro; solve_Countable
  | |- Countable nat => apply nat_Countable
  | _ => try assumption
  end.

