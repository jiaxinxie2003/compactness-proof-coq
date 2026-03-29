(**************************************************************************)
(*  This is part of semantic_pc, it is distributed under the terms of the *)
(*            GNU Lesser General Public License version 3                 *)
(*               (see file LICENSE for more details)                      *)
(*                                                                        *)
(*                       Copyright 2023-2028                              *)
(*         Dakai Guo, qiming Wang, jianghao Liu and Wensheng Yu           *)
(**************************************************************************)

(** semantic_K_System *)

Require Import base_pc.
Require Import formulas_K_System.
Require Import syntax_K_System.
Require Export Coq.Bool.Bool.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Epsilon.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Vectors.Vector.
Import VectorNotations.
Require Import Program.

(* P88 3.3 语义 *)
Class Module := {
  M : Type;
  I_c : Con -> M;
  I_f : forall f, Vector.t M (arity_F f) -> M;
  I_R : forall r, Vector.t M (arity_R r) -> Prop }.

(* 定义 3.3.7 赋值 *)
Definition value (MM: Module) := Var -> M.

(* P91 x重新赋值为m *)
Definition value_v {MM} (v: value MM) x (m: M) := 
  fun (y: Var) => match (classicT (y = x)) with
                   | left _ => m
                   | right _ => v y
                  end.
Notation " v [ x |-> m ] " := (value_v v x m) (at level 0).

(*项t的赋值*)
Fixpoint value_term {MM} (v: value MM) (t: term) : M :=
  match t with
   | Tcon c => I_c c
   | Tvar s => v s
   | Tfun f q => I_f f (Vector.map (value_term v) q)
  end.
Notation " v // " := (value_term v) (at level 0).

Check Vector.map.
(* map : (?A -> ?B) -> forall n : nat, t ?A n -> t ?B n
where ?A : [ |- Type] ?B : [ |- Type] *)

(* 塔斯基语义 可满足关系 |= *)
Fixpoint satisfy_R MM (v: value MM) (p: Formula) : Prop :=
  match p with
   | equality t1 t2 => v// t1 = v// t2
   | atomic r v1 => I_R r (Vector.map (v//) v1)
   | Not q => ~ satisfy_R MM v q
   | Contain q r => (~ satisfy_R MM v q) \/ (satisfy_R MM v r)
   | ForAll x q => forall (m: M), satisfy_R MM (value_v v x m) q 
  end.
Notation " { MM ; v } |= p" :=(satisfy_R MM v p )(at level 0). 

(* P93 引理3.3.18 *)
Lemma L_3_1_1 : forall MM v t1 t2, ~ (v// t1 = v// t2) <-> {MM; v} |= (t1 ≄ t2).
Proof.
  intros. split; intros; red; intros. 
   - apply H.
   - simpl in H. apply H. auto.
Qed. 

Lemma L_3_1_2 : forall MM v p q, 
  {MM; v} |= p /\ {MM; v} |= q <-> {MM; v} |= (p ∧ q).
Proof.
  intros. split; intros.
   - unfold Conjunction. simpl. intro. tauto.
   - split; unfold Conjunction in H; simpl in H; tauto.
Qed.

Lemma L_3_1_3 : forall MM v p q, 
  {MM; v} |= p \/ {MM; v} |= q <-> {MM; v} |= (p ∨ q).
Proof.
  intros. split; intros.
   - unfold Disjunction. simpl. tauto.
   - unfold Conjunction in H; simpl in H; tauto.
Qed.

Lemma L_3_1_4 : forall MM v p q,
  ({MM; v} |= p <-> {MM; v} |= q) <-> {MM; v} |= (p ↔ q).
Proof.
  intros. split; intros.
   - simpl. tauto.
   - simpl in H; tauto.
Qed.

Lemma L_3_1_5 : forall MM v p x (m: M),
  {MM; v} |= (∃ x , p) <-> (exists m, {MM; (value_v v x m)} |= p).
Proof. 
  intros. split; intros.
  - simpl in H. apply not_all_not_ex in H. destruct H. exists x0. auto.
  - simpl. apply ex_not_not_all. destruct H. exists x0. 
    intro. apply H0 in H. inversion H.
Qed.

(* ( MM, v ) |= Γ *)
Definition satisfyable MM v Γ := forall p, p ∈ Γ -> {MM; v} |= p.

(* 可满足定义 *)
(* p可满足 *)
Definition satisfyable_Formula p := exists MM v, {MM; v} |= p.

(* Γ可满足 *)
Definition satisfyable_Γ Γ := exists MM v, satisfyable MM v Γ.

(* 逻辑蕴含 *)
Definition Logically_implies Γ p := 
  forall MM v, satisfyable MM v Γ -> {MM; v} |= p.
Notation "Γ ╞ p" := (Logically_implies Γ p) (at level 80).

(* 逻辑等价 *)
Definition Logically_eqivalent p q := Singleton _ p ╞ q /\ Singleton _ q ╞ p.

(* P94 习题3.3.26 可靠性定理要用到 *)
Example exam_3_4 : forall p q, [/p] ∪ [/p → q] ╞ q.
Proof.
  intros. red. intros. red in H. 
  assert(satisfy_R MM v p /\ satisfy_R MM v (p → q)). 
    { split; apply H. left. apply Single. auto. right. apply Single. auto. } 
  destruct H0. simpl in H1. destruct H1; try contradiction; auto.
Qed.

(* P95 *)
(* 有效式 *)
Definition valid_p p := forall MM v, {MM; v} |= p.
Notation " ╞ p" := (valid_p p) (at level 80). 

Lemma valid_li_eq : forall p, Φ ╞ p <-> ╞ p.
Proof.
  split; intros. red. red in H. intros.
  assert (satisfyable MM v Φ). { red. intros. destruct H0. }
  apply H in H0. auto. red in H. red. intros. auto.
Qed.

(* 矛盾式 *)
Definition contradictory_p p := forall MM v, ~ {MM; v} |= p.

(* P95 评注3.3.31 *)
Corollary valid_fact : forall p, ╞ (p ∨ ¬p).
Proof. 
  intros. red. intros. simpl. destruct (classicT (satisfy_R MM v p)).
  left. auto. right. auto.
Qed.

Corollary contradictory_fact : forall p, contradictory_p (p ∧ ¬p).
Proof.
  intros. red. intros. simpl. destruct (classicT (satisfy_R MM v p)); 
  intro; apply H. right. auto. left. auto.
Qed.

(* P95 习题3.3.35 *)
Corollary eqivalent_calss : forall p q, ╞ p -> ╞ q -> Logically_eqivalent p q.
Proof. red. split; red; intros. apply H0. apply H. Qed.

(* P94 习题3.3.36 可靠性定理要用到 *)
Example exam_3_5 : forall x p, ╞ p <-> ╞ (∀ x, p).
Proof.
  split; red; intros.
   - intro. intros. simpl. intros. apply H.
   - red in H. specialize H with MM v. simpl in H. specialize H with (v x). 
     assert(value_v v x (v x) = v). 
       { apply functional_extensionality_dep. intros. unfold value_v.
         destruct(classicT (x0 = x)). congruence. auto. }
     rewrite H0 in H. auto. 
Qed.

Check functional_extensionality_dep.
(* forall f g : forall x : ?A, ?B x, (forall x : ?A, f x = g x) -> f = g *)

(* P96 习题3.3.38 *)
Example exam_3_6_1 : forall Γ p, Γ ╞ p <-> ~ satisfyable_Γ (Γ ∪ [/¬p]).
Proof.
  intros. split; red; intros.
  - red in H0. destruct H0 as [MM [v H0]].
    assert (satisfyable MM v Γ). { red in H0. red. intros. apply H0. left. auto. } 
    apply H in H1. pose proof H0. red in H0. specialize H0 with ¬p. 
    assert (¬p ∈ (Γ ∪ [/¬p])). { right. eauto with sets. } 
    apply H0 in H3. simpl in H3. auto.
  - red in H. unfold satisfyable_Γ in H. unfold satisfyable in H0.
    destruct (classicT (p ∈ Γ) ). apply H0 in i. auto.
    destruct (classicT (satisfy_R MM v p)). auto.
    assert ((exists (MM: Module) (v: value MM), satisfyable MM v (Γ ∪ [/¬ p]))). 
      { exists MM,v. red. intros. destruct H1. apply H0. auto. apply Single in H1. 
        rewrite H1. apply n0. } 
    apply H in H1. destruct H1.
Qed.

Example exam_3_6_2 : forall Γ p, Γ ╞ ¬p <-> ~ satisfyable_Γ (Γ ∪ [/p]).
Proof.
  intros. split; red; intros.
  - red in H0. destruct H0 as [MM [v H0]].
    assert (satisfyable MM v Γ). 
      { red in H0. red. intros. apply H0. left. auto. } 
    apply H in H1. pose proof H0. red in H0. specialize H0 with p. 
    assert( p ∈ (Γ ∪ [/p])). { right. eauto with sets. } 
    apply H0 in H3. simpl in H1. auto.
  - red in H. unfold satisfyable_Γ in H. unfold satisfyable in H0.
    destruct (classicT (¬p ∈ Γ) ). apply H0 in i. auto.
    destruct (classicT ( satisfy_R MM v ¬p)). auto.
    assert ((exists (MM : Module) (v : value MM), satisfyable MM v (Γ ∪ [/p]))). 
      { exists MM,v. red. intros. destruct H1. apply H0. auto. apply Single in H1.
        rewrite H1. simpl in n0. tauto. }
    apply H in H1. destruct H1.
Qed.

Example exam_3_6_3 : forall Γ p, satisfyable_Γ Γ 
  -> satisfyable_Γ (Γ ∪ [/¬p]) \/ satisfyable_Γ (Γ ∪ [/p]).
Proof.
  intros. destruct (classicT (p ∈ Γ) ); red in H; destruct H as [M [v H0]].
  - right. red. exists M,v. red. intros. destruct H. apply H0. auto. 
    apply Single in H. rewrite H. apply H0. auto.
  - destruct (classicT (satisfy_R M v ¬p)).
    + left. red. exists M,v. red. intros. destruct H. apply H0. 
      auto. apply Single in H. rewrite H. apply s.
    + right. red. exists M,v. red. intros. destruct H. apply H0.
      auto. apply Single in H. rewrite H. tauto.
Qed.


(* P96 合同与代入 *)
(* 在项上合同 *)
Definition agreement_t {MM} (u v: value MM) t := 
  forall x, x ∈ (term_Ens t) -> u x = v x.

(* 在公式上合同 *)
Definition agreement_f {MM} (u v: value MM) p :=
  forall x, x ∈ (Formula_free_Ens p) -> u x = v x.


(* (* 归纳证明 *)
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
End term_ind_process. *)


(* 合同引理 *)
Definition agree_t t := forall MM (u v: value MM), agreement_t u v t
  -> u// t = v// t.

Definition agree_v n (t: Vector.t term n) := forall MM (u v: value MM),
  (forall x, x ∈ (Vector_Ens n t) -> u x = v x) -> map (u//) t = map (v//) t.

Fact agree_1 : forall n, agree_t (Tvar n).
Proof. intros. red. intros. simpl. apply H. simpl. split. Qed.

Fact agree_2 : forall n, agree_t (Tcon n).
Proof. intros. red. intros. simpl. auto. Qed.

Fact agree_3 : forall (t0: Vector.t term 0), agree_v 0 t0.
Proof.
  intros. red. intros. apply case0. set(fun t1 => map (value_term u) t1 = nil _). 
  apply (case0 P). unfold P. simpl. auto. 
Qed. 

Fact agree_4 : forall (f: Fun) (v: Vector.t term (arity_F f)),
  agree_v (arity_F f) v -> agree_t (Tfun f v).
Proof.
  intros. red. intros. red in H. simpl. f_equal. apply H.
  intros. red in H0. apply H0. apply H1.
Qed.

Fact agree_5 : forall n (t0: term) (t1: Vector.t term n),
  agree_t t0 -> agree_v n t1 -> agree_v (S n) (t0 :: t1).
Proof.
  intros. red. intros. simpl. unfold agree_t in H. f_equal. 
  apply H. red. intros. apply H1. simpl. left. auto.
  red in H0. apply H0. intros. apply H1. simpl. right. auto.
Qed.

(* 合同引理1 *)
Theorem agree_fact_1 : forall t, agree_t t.
Proof.
  intros. apply Term_ind_new with agree_v.
  - apply agree_1. 
  - apply agree_2.
  - apply agree_3.
  - apply agree_4.
  - apply agree_5.
Qed.

(* 项向量合同 *)
Corollary agree_6 : forall n v, agree_v n v.
Proof.
  red. intros. induction v.
  - apply agree_3. intros. destruct H0.
  - simpl. f_equal. apply agree_fact_1. red. intros. 
    apply H. simpl. left; auto. apply IHv. intros. apply H. 
    simpl. right; auto.
Qed.

(* 合同引理2 *)
Theorem agree_fact_2 : forall MM p u v, agreement_f u v p 
  -> ({MM; u} |= p <-> {MM; v} |= p).
Proof.
  intros MM. induction p.  
  - split; intros; simpl in H0; red; red in H. 
    assert(value_term u t = value_term v t /\ value_term u t0 = value_term v t0).
      { split; apply agree_fact_1; red; intros; apply H; simpl.
        left; auto. right; auto. } 
    destruct H1; congruence.
    assert(value_term u t = value_term v t /\ value_term u t0 = value_term v t0).
      { split; apply agree_fact_1; red; intros; apply H; simpl.
        left; auto. right; auto. } 
    destruct H1; congruence.
  - split; intros; simpl; red in H0; pose proof(agree_6 _ t); red in H1; 
    assert(map (value_term u) t = map (value_term v) t) by
     (apply H1;intros; apply H; simpl; apply H2). 
    rewrite H2 in H0. auto. rewrite H2. auto.
  - intros. assert(agreement_f u v p). { red. intros. apply H. simpl. auto. } 
    apply IHp in H0. simpl. apply not_iff_compat. auto.
  - simpl. intros. 
    assert(agreement_f u v p1 /\ agreement_f u v p2).
      { split;red; intros; apply H; simpl. left. auto. right. auto. }
    destruct H0. apply IHp1 in H0. apply IHp2 in H1. split; tauto.
  - intros. simpl in H. 
    assert(forall m, agreement_f (value_v u v m) (value_v v0 v m) p).
      { intros. red. intros. red in H. simpl in H. unfold value_v.
        destruct(classicT (x = v)). auto. apply H. unfold Setminus. split; auto. 
        intro. assert(x = v) by (apply Single in H1;auto). contradiction. } 
    simpl. split; intros; simpl; simpl in H1; intros; specialize H0 with m; 
    specialize H1 with m; pose proof (IHp (value_v u v m) (value_v v0 v m) H0);
    destruct H2. apply H2. auto. apply H3. auto.
Qed.


(* 项替换引理 *)
Definition sub_t t := forall MM (u: value MM) t' x,
  u //(t {x ; t'}) = (u [x |-> (u // t')])// t.

(* 向量项替换引理*)
Definition sub_v n (v: Vector.t (term) n) := forall MM (u: value MM) x t', 
  Vector.map (u//) (substitute_v n v t' x) 
    = Vector.map ((u [x |-> (u // t')])//) v.

Fact eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof. intros x y. apply iff_reflect. symmetry. apply Nat.eqb_eq. Qed.

Fact eqbv_reflect : forall (m n: Var), reflect (m = n) (eqbv m n).
Proof.
  intros. apply iff_reflect. split; intros; destruct m, n.
  - inversion H. simpl. destruct (eqb_reflect n n); auto.
  - inversion H. f_equal. destruct (eqb_reflect n0 n); auto. inversion H1.
Qed.

Fact eqbc_reflect : forall (m n: Con), reflect (m = n) (eqbc m n).
Proof.
  intros. apply iff_reflect. split; intros; destruct m, n.
  - inversion H. simpl. destruct (eqb_reflect n n); auto.
  - inversion H. f_equal. destruct (eqb_reflect n0 n); auto. inversion H1.
Qed.
Global Hint Resolve eqb_reflect eqbv_reflect eqbc_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct 
     | destruct H as [H|H]; 
       [| try first [apply not_eq in H]]].

Fact sub_1 : forall n, sub_t (Tvar n).
Proof.
  red. intros. simpl. destruct(eqbv x n) eqn:E.
  - unfold value_v. bdestruct (eqbv x n). subst. destruct classicT.
    + auto. 
    + tauto.
    + inversion E.
  - unfold value_v. bdestruct (eqbv x n). destruct classicT.
    + inversion E.
    + tauto.
    + simpl. destruct classicT; try tauto. subst; tauto. 
Qed.

Fact sub_2 : forall n, sub_t (Tcon n).
Proof. red. intros. simpl. auto. Qed.

Fact sub_3 : forall (t0: Vector.t term 0), sub_v 0 t0.
Proof.
  red. intros. apply case0. 
  set(fun t1 => Vector.map (u//) (substitute_v 0 t1 t' x) = nil M). 
  apply (case0 P). unfold P. simpl. auto. 
Qed.

Fact sub_4 : forall (f: Fun) (v: Vector.t term (arity_F f)),
  sub_v (arity_F f) v -> sub_t (Tfun f v).
Proof. intros. red. intros. simpl. f_equal. apply H. Qed.

Fact sub_5 : forall n (t0: term) (t1: Vector.t term n),
  sub_t t0 -> sub_v n t1 -> sub_v (S n) (t0 :: t1).
Proof.
  intros. red. intros. red in H,H0. pose proof (H MM u t' x). 
  pose proof (H0 MM u x t'). simpl. congruence.
Qed.

(* 项替换定理 *)
Theorem term_substitution_theorem : forall t, sub_t t. 
Proof.
  apply Term_ind_new with sub_v.
  - apply sub_1.
  - apply sub_2.
  - apply sub_3.
  - apply sub_4.
  - apply sub_5.
Qed.

(* 项向量替换定理 *)
Corollary sub_6 : forall n v, sub_v n v.
Proof.
  intros. red. intros. induction v.
  - apply sub_3. 
  - simpl. pose proof (term_substitution_theorem h MM u t' x). congruence. 
Qed.

(* Definition sub_tx t := forall x t', ~ x ∈ (term_Ens t) 
  -> substitute_t t t' x = t.
Definition sub_vx n (v: Vector.t term n) := 
  forall x t', ~ x ∈ (Vector_Ens _ v) -> substitute_v _ v t' x = v. 

Fact sub_tx_1 : forall n, sub_tx (Tvar n).
Proof.
  intros. red. intros. simpl. bdestruct (eqbv x n); auto. subst.
  elim H. simpl. constructor.
Qed.

Fact sub_tx_2 : forall n, sub_tx (Tcon n).
Proof. red. auto. Qed.

(* Print Vector.t. *)

Fact sub_tx_3 : forall (t: Vector.t term 0), sub_vx 0 t.
Proof.
  red. intros. apply case0. 
  set(fun t => substitute_v 0 t t' x = Vector.nil term).
  apply (case0 P). unfold P. simpl. auto.
Qed.

Fact sub_tx_4 : forall (f: Fun) (v: Vector.t term (arity_F f)), 
  sub_vx (arity_F f) v -> sub_tx (Tfun f v).
Proof.
  red. intros. simpl. f_equal. red in H. apply H. simpl in H0. apply H0.
Qed.

Fact sub_tx_5 : forall n (t: term) (t0: Vector.t term n), 
  sub_tx t -> sub_vx n t0 -> sub_vx (S n) (t :: t0).
Proof.
  intros. red in H,H0. red. intros. simpl. simpl in H1. 
  assert((~ x ∈ (term_Ens t)) /\ (~ x ∈ (Vector_Ens n t0))). 
    { split; intro; elim H1. left. auto. right. auto. }
  destruct H2. apply H with (x := x) (t' := t') in H2.
  apply H0 with (x := x)(t' := t') in H3. congruence.
Qed.

Fact bound_sub_t : forall t , sub_tx t.
Proof.
  apply Term_ind_new with sub_vx.
  - apply sub_tx_1.
  - apply sub_tx_2.
  - apply sub_tx_3.
  - apply sub_tx_4.
  - apply sub_tx_5.
Qed.

Fact sub_tx_6 : forall n x (v: Vector.t term n) t',  
  ~ x ∈ (Vector_Ens _ v) -> substitute_v _ v t' x = v.
Proof.
  intros. induction v. apply sub_tx_3. auto. simpl. simpl in H.
  assert(substitute_t h t' x = h /\ substitute_v n v t' x = v).
    { split. pose proof (bound_sub_t h x t'). apply H0. intro.
      elim H. left. auto. apply IHv. intro. elim H. right. auto. }
  destruct H0; congruence.
Qed.

Fact bound_sub : forall x p t, 
  ~ x ∈ (Formula_free_Ens p) -> substitute_f p t x = p.
Proof.
  intros. induction p.
  - simpl. assert(((substitute_t t0 t x) = t0) /\ (substitute_t t1 t x) = t1). 
      { split; apply bound_sub_t; simpl in H; intro; elim H.
        left. auto. right. auto. } 
    destruct H0. congruence.
  - simpl. f_equal. simpl in H. apply sub_tx_6. auto.
  - simpl. f_equal. simpl in H. apply IHp. apply H.
  - simpl. f_equal. simpl in H. apply IHp1. intro. elim H. 
    left. auto. apply IHp2. intro. elim H. right. auto.
  - simpl. destruct (eqbv x v) eqn:E. auto. f_equal. apply IHp.
    intro. elim H. simpl. split. auto. intro. apply Single in H1.
    bdestruct (eqbv x v). inversion E. contradiction.
Qed. *)

(* Print value_v.
Print value_term. *)

(* Corollary Single : forall {U} (a x: U), a ∈ [/x] <-> a = x.
Proof. split; intros. destruct H; auto. rewrite H. split. Qed.
 *)

(* 公式替换定理*)
Theorem formula_substitution_theorem: forall MM p t x, t_x_free p t x = true
  -> (forall u, satisfy_R MM u (substitute_f p t x)
        <-> satisfy_R MM (value_v u x (value_term u t)) p).
Proof.
  intros. generalize dependent u. induction p.
  - split; intros; simpl; simpl in H0.
    + repeat rewrite <- term_substitution_theorem. auto.
    + repeat rewrite term_substitution_theorem. auto.
  - split; intros; simpl; simpl in H0.
    + rewrite sub_6 in H0. auto.
    + rewrite sub_6. auto.
  - simpl in H. simpl. intros. apply not_iff_compat. 
    generalize dependent u. apply IHp. auto.
  - simpl in H. apply andb_prop in H. destruct H.
    intros. apply IHp1 with u in H. apply IHp2 with u in H0. simpl. split; tauto.
  - rename v into y. simpl in H. 
    destruct (classicT (x ∈ (Formula_free_Ens p) ~ [/y])).
    + simpl. destruct (classicT(y ∈ (term_Ens t))). inversion H.
      intros. destruct(eqbv x y) eqn:E.
      * bdestruct (eqbv x y); subst; auto.
        assert(y ∈ [/y]). { apply Single. auto. }
        destruct i; auto. destruct H2; auto. inversion E.
      * assert (forall m, value_v (value_v u y m) x (value_term u t) 
          = value_v (value_v u x (value_term u t)) y m). 
          { intros. apply functional_extensionality_dep. intros.
            unfold value_v. destruct (classicT(x0 = x)).
            + destruct (classicT(x0 = y)).
              rewrite e in e0. bdestruct (eqbv x y). inversion E. tauto. auto.
            + destruct (classicT(x0 = y)); auto. } 
        split; intros.
        ** simpl in H1. specialize H1 with m.
           pose proof (IHp H (value_v u y m)). destruct H2.
           apply H2 in H1. clear H2. clear H3.
           pose proof(agree_fact_1 t MM u ((value_v u y m))).
           assert(agreement_t u (value_v u y m) t). { red.
           intros. unfold value_v. destruct(classicT (x0 = y)).
           rewrite e in H3. apply n in H3. inversion H3. auto. }
           apply H2 in H3. rewrite <-H3 in H1. 
           specialize H0 with m. rewrite H0 in H1. auto.
        ** simpl. intros. specialize H1 with m.
           pose proof (IHp H (value_v u y m)). destruct H2. 
           clear H2. apply H3. pose proof 
           (agree_fact_1 t MM u ((value_v u y m))).
           assert(agreement_t u (value_v u y m) t). { red. 
           intros. unfold value_v. destruct (classicT (x0 = y)).
           rewrite e in H4. apply n in H4. inversion H4. auto. }
           apply H2 in H4. rewrite <- H4. specialize H0 with m.
           rewrite <- H0 in H1. auto.
    + intros. unfold substitute_f. assert(agreement_f u 
      (value_v u x (value_term u t)) (∀ y, p)). { red.
      intros. unfold value_v. destruct (classicT(x0 = x)).
      rewrite e in H0. apply n in H0. inversion H0. auto. }
      destruct (eqbv x y) eqn:E.
      * pose proof (agree_fact_2 MM (∀ y, p) u (value_v u x (value_term u t))). 
        apply H1 in H0. auto.
      * assert(~ x ∈ (Formula_free_Ens p)). 
          { intro. elim n. split. auto. intro. apply Single in H2. 
            bdestruct (eqbv x y); auto. inversion E. }
        apply subst_f_ignore with (t := t) in H1. fold substitute_f. rewrite H1. 
        pose proof (agree_fact_2 MM (∀ y, p) u (value_v u x (value_term u t))).
        apply H2 in H0. auto.
Qed.



(* P106 常见的有效式 *)
(* 定理 3.3.64 联词类有效式 *)
(* 习题 3.3.66 联词类有效式 可靠性定理用到*)
Theorem T_3_6_1 : forall p q, ╞ p → q → p.
Proof.
  intros. red. intros. simpl. destruct (classicT (satisfy_R MM v p)). 
  - right; right; auto.
  - left; auto.
Qed.

Fact notand_ornot : forall P Q, ~ (P /\ Q) <-> ~ P \/ ~ Q.
Proof.
  intros; split.
  - intros. elim (classic P); auto.
  - simple induction 1; red; simple induction 2; auto.
Qed.

Fact notor_andnot : forall P Q, ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof. tauto. Qed.

Fact NNPP : forall P, ~ ~ P <-> P.
Proof.
  split. intros. 
  - destruct (classicT P).
    + auto.
    + apply H in n. inversion n.
  - intros. intro. contradiction.
Qed.

Theorem T_3_6_2 : forall p q r, ╞ ((p → (q → r)) → (p → q) → (p → r)).
Proof.
  intros. red. intros. simpl. destruct (classicT (satisfy_R MM v p)). 
  - destruct (classicT (satisfy_R MM v r)). 
    + right; right; right; auto.
    + destruct (classicT (satisfy_R MM v q)).
      * left. rewrite notor_andnot. rewrite NNPP. tauto.
      * right; left. rewrite notor_andnot. rewrite NNPP. tauto.
  - right; right; left; auto.
Qed.

Theorem T_3_6_3: forall p q , ╞ ((¬p → q) → (¬p → ¬q) → p).
Proof.
  intros. red. intros. simpl. rewrite NNPP; try exact (satisfy_R MM v p). 
  repeat (rewrite notor_andnot). destruct (classicT (satisfy_R MM v p));
  destruct (classicT (satisfy_R MM v q)); tauto.
Qed.

(* 定理 3.3.67 等词类有效式 可靠性定理用到 *)
Theorem T_3_7_1 : forall t , ╞ t ≃ t.
Proof. intros. red. intros. simpl. auto. Qed.

Theorem T_3_7_2 : forall t1 t2, ╞ (t1 ≃ t2) → (t2 ≃ t1).
Proof.
  intros. red. intros. simpl. 
  destruct (classicT (value_term v t2 = value_term v t1)).
  right; auto. left; auto.
Qed.

Theorem T_3_7_3 : forall t1 t2 t3, ╞ (t1 ≃ t2) → (t2 ≃ t3) → (t1 ≃ t3).
Proof.
  intros. red. intros. simpl. 
  destruct (classicT (value_term v t1 = value_term v t3)).
  - right; right; auto.
  - destruct (classicT (value_term v t2 = value_term v t1)).
    + right; left. rewrite <- e in n. auto.
    + left. auto.
Qed.

(* Print equality_4. *)

(* {MM; v} |= equality_4 p v1 v2
   等价于 (如果 v1 和 v2 的语义值相等，则 {MM; v} |= p) *)
Lemma equality_4' : forall m v1 v2 p MM v,
  {MM; v} |= (equality_4 p m m v1 v2) <->
  (map v // v1 = map v // v2 -> {MM; v} |= p).
Proof.
  induction v1; intros; dependent destruction v2; simpl.
  - split; intros; auto.
  - split; intros.
    + dependent destruction H0. destruct H. contradiction.
      apply (IHv1 v2 p MM v); auto.
    + destruct (classicT (v // h = v // h0)); auto. right. apply IHv1.
      intro. apply H. f_equal; auto.
Qed.

Theorem T_3_7_4 : forall r v1 v2 ,
  ╞ (equality_4 ((atomic r v1) → (atomic r v2)) _ _ v1 v2).
Proof.
  unfold valid_p. intros. apply equality_4'. intros.
  simpl. destruct (classicT (I_R r (map v // v1))); auto.
  right. rewrite H in i. auto.
Qed.

Theorem T_3_7_5 : forall f v1 v2,
  ╞ (equality_4 (equality (Tfun f v1) (Tfun f v2)) _ _ v1 v2).
Proof.
  intros. unfold valid_p. intros. eapply equality_4'; eauto. intros.
  simpl. f_equal. auto.
Qed.


(* 定理 3.3.73 量词分配类有效式 可靠性定理用到*)
Theorem T_3_8: forall p q x, ╞ (∀ x, (p → q)) → ((∀ x, p) → (∀ x, q)).
Proof.
  red. intros. simpl. 
  destruct (classicT (forall m: M, satisfy_R MM (value_v v x m) p)); 
  destruct(classicT (forall m : M, satisfy_R MM (value_v v x m) q)).
  - tauto.
  - apply not_all_ex_not in n. left. intro. destruct n. 
    specialize H with x0. specialize s with x0. destruct H; contradiction.
  - tauto.
  - tauto.
Qed.

(* 定理 3.3.76 量词消去类有效式 *)

(* 定理 3.3.79 代入类有效式 可靠性定理用到*)
Theorem T_3_9 : forall p x t, t_x_free p t x = true -> ╞ (∀ x, p) → p{x;;t}.
Proof.
  intros. red. intros. simpl.
  destruct (classicT (forall m: M, satisfy_R MM (value_v v x m) p)).
  - right. specialize s with (value_term v t).
    apply formula_substitution_theorem; auto.
  - tauto.
Qed.

