(* ----------------------------------------------------------------- *)
(*               Transparent Computable Definitions                  *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Base.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.


(* Copy of unlockable to reflect definition from evaluable ones *)
#[universes(template)]
Structure evaluable T v := Evaluable {evaled : T; _ : evaled = v}.

Lemma evals T x C : @evaled T x C = x. by case: C. Qed.


Definition evidP (b: bool): reflect b b :=
  if b
  then ReflectT true is_true_true
  else ReflectF false not_false_is_true.
Arguments evidP {b}.


Program Canonical idP_eval b := Evaluable (_: @evidP b = @idP b).
Next Obligation.
  move: idP. case: b=> /= p;
  refine (match p with ReflectT _ => _ | ReflectF _ => _ end)=> //.
  all: f_equal; apply/proof_irrelevance.
Qed.


Section SubType.
Variable T: Type.
Variable P: pred T.
Variable sT: subType P.

Definition sembed x :=
  if evidP is ReflectT Px then Some (Sub (sT := sT) x Px) else None.

Program Canonical insub_eval v := Evaluable (_: sembed v = insub v).
Next Obligation. rewrite /sembed /insub evals //. Qed.

End SubType.
Arguments sembed {T P sT} x.


Section Ordinal.
Variable n: nat.

Definition enumOrd: seq (ordinal n) := pmap sembed (iota 0 n).

Program Canonical enum_ord_eval := Evaluable (_: enumOrd = enum 'I_n).
Next Obligation.
  rewrite /enumOrd enumT unlock /= /ord_enum.
  apply/eq_pmap=> ?. rewrite evals //.
Qed.


Program Definition tupleOrd: (n.-tuple 'I_n) := @Tuple _ _ enumOrd _.
Next Obligation. rewrite evals. apply/eqP/size_enum_ord. Qed.

Program Canonical ord_tuple_eval := Evaluable (_: tupleOrd = ord_tuple n).
Next Obligation. apply /val_inj. rewrite /= evals //. Qed.


Definition tupleOf `(f: 'I_n -> T) := map_tuple f tupleOrd.

Program Canonical mktuple_eval `(f: 'I_n -> T) := Evaluable (_: tupleOf f = mktuple f).
Next Obligation. rewrite /tupleOf evals //. Qed.

End Ordinal.


Notation "n '.-ord' i" := (Ordinal (n:=n) (m:=i) is_true_true) (at level 10).

