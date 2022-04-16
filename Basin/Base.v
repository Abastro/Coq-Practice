(* ----------------------------------------------------------------- *)
(*                   Mainly classical Base module                    *)
(* ----------------------------------------------------------------- *)

From Coq Require Export RelationClasses.

From mathcomp Require Export ssreflect ssrfun ssrbool.
From mathcomp Require Export eqtype fintype ssrnat seq tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

Axiom proof_irrelevance: forall (P: Prop) (p1 p2: P), p1 = p2.

(*

Property setoid_refl `(Setoid U): forall x, x == x.
Proof. reflexivity. Qed.
Property setoid_sym `(Setoid U): forall x y, x == y -> y == x.
Proof. symmetry. auto. Qed.
Property setoid_trans `(Setoid U): forall x y z, x == y -> y == z -> x == z.
Proof. etransitivity; eauto. Qed.

#[export]
Hint Immediate setoid_refl setoid_sym setoid_trans: core.


Axiom proof_irrelevance: forall P: Prop, forall pf pf': P, pf = pf'.


(* Setoid for leibniz equality *)

Class UsualSetoid (U:Type) := {}.

Instance usual_sum `(UsualSetoid U) `(UsualSetoid V): UsualSetoid (U + V). Qed.
Instance usual_prod `(UsualSetoid U) `(UsualSetoid V): UsualSetoid (U * V). Qed.

Instance usual_nat: UsualSetoid nat. Qed.

Instance usual_sig `(UsualSetoid U) (P: U -> Prop): UsualSetoid (sig P). Qed.


Program Instance setoid_usual `(UsualSetoid U): Setoid U := {
  equiv := eq
}.

Property usualeq_spec: forall `(UsualSetoid U) (x y: U), (x == y) = (x = y).
Proof. reflexivity. Qed.


(* Sig type - TODO: Migrate to ssreflect *)

Definition mkSig `(x: U) {P: U -> Prop} (pf: P x): {x | P x} :=
  exist P x pf.
Definition get `(pf: {x: U | P x}): U :=
  proj1_sig pf.
Definition getPr `(pf: {x: U | P x}): P (get pf) :=
  proj2_sig pf.

Property sig_eq_iff: forall U P (x y: { t: U | P t }),
  x = y <-> get x = get y.
Proof. split.
  - move=> ->. reflexivity.
  - case: x y=> [xi xp] [yi yp]. simpl.
    move: xp yp => + + E. rewrite E => xp yp.
    f_equal. apply: proof_irrelevance.
Qed.


(* Function type considered normal setoid *)

Program Instance setoid_function U `(Setoid V): Setoid (U -> V) := {
  equiv := fun f g => forall u, f u == g u }.
Next Obligation. split; red; eauto. Qed.
Add Parametric Morphism U `(Setoid V): (fun (f: U -> V) (x: U) => f x)
  with signature equiv ==> eq ==> equiv as apply_mor.
Proof. auto. Qed.


#[export]
Hint Unfold setoid_usual setoid_function: core.
#[export]
Hint Resolve usualeq_spec sig_eq_iff: core.


(* Aid on unique existence *)
Lemma unique_by_uniqueness: forall U (P: U -> Prop) u,
  P u -> uniqueness P -> unique P u.
Proof. firstorder. Qed.



(* ----------------------------------------------------------------- *)
(*                          More on Logics                           *)
(* ----------------------------------------------------------------- *)

Lemma is_true_fold: forall p: bool, (p = true) = p.
Proof. reflexivity. Qed.

Instance trans_gt : Transitive gt := flip_Transitive _.

*)
