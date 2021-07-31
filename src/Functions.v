Require Import Basics.
Require Import Setoid.
Require Import RelationClasses.

Module Function_Extras.

(* Extensional equality on certain predicate *)
Definition gen_ext_eq {U:Type} {V:Type} (P: U -> Prop) (e: relation V): relation (U -> V) :=
  fun f g => forall x: U, P x -> e (f x) (g x).

Instance gen_ext_eq_port U V (P: U -> Prop) (e: relation V) `(Equivalence _ e):
  Equivalence (gen_ext_eq P e).
Proof. unfold gen_ext_eq. split.
  - unfold Reflexive. intros. reflexivity.
  - unfold Symmetric. intros. symmetry. auto.
  - unfold Transitive. intros. etransitivity; eauto.
Qed.

Add Parametric Relation U V P e `(Equivalence _ e): (U -> V) (gen_ext_eq P e)
  reflexivity proved by reflexivity
  symmetry proved by symmetry
  transitivity proved by transitivity
  as eq_gen_fun.


(* Extensional equality *)
Definition ext_eq {U:Type} {V:Type} (e: relation V): relation (U -> V) :=
  fun f g => forall x: U, e (f x) (g x).

Property ext_eq_speced: forall U V (e: relation V) f g,
  ext_eq e f g <-> gen_ext_eq (@const Prop U True) e f g.
Proof. unfold gen_ext_eq, ext_eq. split; intros; apply H. unfold const. trivial. Qed.

Instance ext_eq_port U V (e: relation V) `(Equivalence _ e):
  Equivalence (@ext_eq U V e).
Proof. unfold ext_eq. split.
  - unfold Reflexive. intros. reflexivity.
  - unfold Symmetric. intros. symmetry. auto.
  - unfold Transitive. intros. etransitivity; eauto.
Qed.

Add Parametric Relation U V e `(Equivalence _ e): (U -> V) (ext_eq e)
  reflexivity proved by reflexivity
  symmetry proved by symmetry
  transitivity proved by transitivity
  as eq_fun.

Definition def_ext_eq {U:Type} {V:Type} := @ext_eq U V eq.

#[export]
Hint Unfold gen_ext_eq ext_eq def_ext_eq: core.

End Function_Extras.
