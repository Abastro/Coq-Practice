Require Import Basics.
Require Import Setoid.
Require Import RelationClasses.

(* Rewrite tactics *)
(* Setoid_rewrites all occurrences, until it meets True. Renames hypothesis. *)
Ltac all_rewrite := let BLOCK := True in
  let rec rec_rewrite :=
    lazymatch goal with
    | [ |- BLOCK -> _ ] => intros _
    | [ |- ?R ?x ?y -> _ ] =>
      let E := fresh "E" in intros E; try setoid_rewrite E; rec_rewrite
    end in
  generalize (I : BLOCK);
  repeat match goal with
  | [ E: ?R ?x ?y |- _ ] => revert E
  end; rec_rewrite.

(* Rewrites all occurrences to match for reflexivity. *)
Ltac rw_refl := all_rewrite; reflexivity.

(* From https://github.com/KiJeong-Lim/DschingisKhan *)
Class Setoid (U:Type) := {
  eqs: U -> U -> Prop
; setoid_equiv:> Equivalence eqs
}.

Add Parametric Relation U `(Setoid U): U eqs
  reflexivity proved by reflexivity
  symmetry proved by symmetry
  transitivity proved by transitivity
  as setoid_rel.

Notation "x '= y" := (eqs x y) (at level 80, no associativity).

Property setoid_refl (U:Type) `(Setoid U): forall x, x '= x.
Proof. reflexivity. Qed.
Property setoid_sym (U:Type) `(Setoid U): forall x y, x '= y -> y '= x.
Proof. symmetry. auto. Qed.
Property setoid_trans (U:Type) `(Setoid U): forall x y z, x '= y -> y '= z -> x '= z.
Proof. etransitivity; eauto. Qed.

#[export]
Hint Resolve setoid_refl setoid_sym setoid_trans: core.

(* Setoid for leibniz equality *)

Class UsualSetoid (U:Type) := {}.

Program Instance setoid_usual U `(UsualSetoid U): Setoid U := {
  eqs := eq
}.

(* Prop, Function, Subset *)

Program Instance setoid_prop: Setoid Prop := {
  eqs := fun P Q => P <-> Q }.
Next Obligation. split; red; tauto. Qed.

Program Instance setoid_function U V `(Setoid V): Setoid (U -> V) := {
  eqs := fun f g => forall u, f u '= g u }.
Next Obligation. split; red; eauto. Qed.
Add Parametric Morphism U V `(Setoid V): (fun (f: U -> V) (x: U) => f x)
  with signature eqs ==> eq ==> eqs as apply_mor.
Proof. auto. Qed.

Program Instance setoid_sub U (P: U -> Prop) `(Setoid U): Setoid (sig P) := {
  eqs := fun x y => proj1_sig x '= proj1_sig y
}.
Next Obligation. split; red; eauto. Qed.

(* Shorthand for sig types *)
Definition get {U:Type} {P: U -> Prop} (pf: sig P): U
  := proj1_sig pf.
Definition getPr {U:Type} {P: U -> Prop} (pf: sig P): P (get pf)
  := proj2_sig pf.
Add Parametric Morphism U (P: U -> Prop) `(Setoid U): (@get U P)
  with signature eqs ==> eqs as get_mor.
Proof. auto. Qed.

(* Injecitivity and Surjectivity *)
Section Func.
Context {U:Type} {V:Type}.

Definition injective (f: U -> V) := forall x x', f x = f x' -> x = x'.
Definition surjective (f: U -> V) := forall y, exists x, y = f x.

Definition inj_setoid `{Setoid U} `{Setoid V} (f: U -> V) :=
  forall x x', f x '= f x' -> x '= x'.
Definition surj_setoid `{Setoid V} (f: U -> V) :=
  forall y, exists x, y '= f x.

End Func.

Lemma get_setoid_inj: forall U P `(Setoid U), inj_setoid (@get U P).
Proof. unfold inj_setoid. intros. unfold eqs, setoid_sub. auto. Qed.

#[export]
Hint Unfold eqs setoid_usual setoid_prop setoid_function setoid_sub
  injective surjective: core.
#[export]
Hint Resolve get_setoid_inj: core.


(* Extensional equality on certain predicate *)
Definition gen_ext_eq {U:Type} {V:Type} (P: U -> Prop) (e: relation V): relation (U -> V) :=
  fun f g => forall x: U, P x -> e (f x) (g x).

Instance gen_ext_eq_port U V (P: U -> Prop) (e: relation V) `(Equivalence _ e):
  Equivalence (gen_ext_eq P e).
Proof. split; red; unfold gen_ext_eq.
  - reflexivity.
  - symmetry. auto.
  - etransitivity; eauto.
Qed.

Add Parametric Relation U V P e `(Equivalence _ e): (U -> V) (gen_ext_eq P e)
  reflexivity proved by reflexivity
  symmetry proved by symmetry
  transitivity proved by transitivity
  as eq_gen_fun.

#[export]
Hint Unfold gen_ext_eq: core.



(* Uniqueness on Type gives rise to partial functions *)
Module Unique_Extras.

Definition sig_uniq {A:Type} (P: A -> Prop) := sig (unique P).

Notation "'uniq' x , p" := (sig_uniq (fun x => p))
  (at level 200, x binder, right associativity): type_scope.

Lemma sigma_to_unique (A: Type) (P: A -> Prop) :
  uniqueness P -> {x | P x} -> uniq x, P x.
Proof. intros H [x K]. exists x. split; auto. Qed.

Property get_unique_spec (A: Type) (P: A -> Prop) (E: uniq x, P x): unique P (get E).
Proof. destruct E. auto. Qed.

#[export]
Hint Resolve sigma_to_unique get_unique_spec : core.

End Unique_Extras.