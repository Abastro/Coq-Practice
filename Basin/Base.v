Require Export Basics.
Require Export Setoid.
Require Export SetoidClass.
Require Export RelationClasses.

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

Property setoid_refl (U:Type) `(Setoid U): forall x, x == x.
Proof. reflexivity. Qed.
Property setoid_sym (U:Type) `(Setoid U): forall x y, x == y -> y == x.
Proof. symmetry. auto. Qed.
Property setoid_trans (U:Type) `(Setoid U): forall x y z, x == y -> y == z -> x == z.
Proof. etransitivity; eauto. Qed.

#[export]
Hint Immediate setoid_refl setoid_sym setoid_trans: core.


(* Setoid for leibniz equality *)

Class UsualSetoid (U:Type) := {}.

Instance usual_prod U V `(UsualSetoid U) `(UsualSetoid V): UsualSetoid (U * V). Qed.

Program Instance setoid_usual U `(UsualSetoid U): Setoid U := {
  equiv := eq
}.

Property usualeq_spec: forall U `(UsualSetoid U) (x y: U), (x == y) = (x = y).
Proof. reflexivity. Qed.

(* Function, Subset *)

Program Instance setoid_function U V `(Setoid V): Setoid (U -> V) := {
  equiv := fun f g => forall u, f u == g u }.
Next Obligation. split; red; eauto. Qed.
Add Parametric Morphism U V `(Setoid V): (fun (f: U -> V) (x: U) => f x)
  with signature equiv ==> eq ==> equiv as apply_mor.
Proof. auto. Qed.

Program Instance setoid_sub U (P: U -> Prop) `(Setoid U): Setoid (sig P) := {
  equiv := fun x y => proj1_sig x == proj1_sig y
}.
Next Obligation. split; red; eauto. Qed.

(* Shorthand for sig types *)
Definition get {U:Type} {P: U -> Prop} (pf: sig P): U
  := proj1_sig pf.
Definition getPr {U:Type} {P: U -> Prop} (pf: sig P): P (get pf)
  := proj2_sig pf.
Add Parametric Morphism U (P: U -> Prop) `(Setoid U): (@get U P)
  with signature equiv ==> equiv as get_mor.
Proof. auto. Qed.

#[export]
Hint Unfold setoid_usual setoid_function setoid_sub: core.
#[export]
Hint Resolve usualeq_spec: core.


(* Definition lift1 {A S T} (f: S -> T): (A -> S) -> (A -> T) := fun x => (f x). *)


(* Below may not be used *)

Fixpoint generalize_all {T} (l: Tlist) (x: T): arrows l T :=
  match l with
  | Tnil => x
  | Tcons A tl => fun a => generalize_all tl x
  end.

Fixpoint pointwise_ext {S T} (f: S -> T) (l: Tlist):
  arrows l S -> arrows l T :=
  match l with
  | Tnil => fun a => f a
  | Tcons A tl => fun a => fun x => pointwise_ext f tl (a x)
  end.

Fixpoint pointwise_ext2 {S T U} (op: S -> T -> U) (l: Tlist):
  arrows l S -> arrows l T -> arrows l U :=
  match l with
  | Tnil => fun a b => op a b
  | Tcons A tl => fun a b => fun x => pointwise_ext2 op tl (a x) (b x)
  end.


Notation "'[:' U , .. , V ':]'" := (Tcons U .. (Tcons V Tnil) ..)
  (at level 0, no associativity): type_scope.


#[export]
Hint Unfold generalize_all pointwise_ext pointwise_ext2: core.
