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
