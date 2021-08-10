From Practice Require Import Basin.Base.
From Practice Require Import Basin.DecClass.
From Practice Require Import Basin.Sets.

Require Import List.

Notation "'{'' x 'in' A '|' P ''}'" :=
  ( A //\\ mkSet (fun x => P) )
  (at level 0, x binder, no associativity).

Definition some := fun '(x, y) => x + y.


(* Notation "'{':' E '|' x .. y 'in' P ''}'" :=
  ( Indexed P ( fun p => let (x , .. , y) := p in E ) ))
  (at level 0, x binder, y binder, no associativity). *)

Lemma setnot_comm: forall U V W (P: ESet U) (Q: ESet V) (F: U * V -> ESet W),
  {'' F x y | x y in P ** Q '} == {'' F x y | y x in Q ** P '}.
