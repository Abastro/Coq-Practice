(* ----------------------------------------------------------------- *)
(*                   Mainly classical Base module                    *)
(* ----------------------------------------------------------------- *)

Require Export Basics.
Require Export Setoid.
Require Export SetoidClass.
Require Export RelationClasses.

Require Export PeanoNat.
Require Export Lia.

Require Import List.
Import ListNotations.


Generalizable All Variables.

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


(* Sig type *)

Definition mkSig `(x: U) {P: U -> Prop} (pf: P x): {x | P x} :=
  exist P x pf.
Definition get `(pf: {x: U | P x}): U :=
  proj1_sig pf.
Definition getPr `(pf: {x: U | P x}): P (get pf) :=
  proj2_sig pf.

Property sig_eq_iff: forall U P (x y: { t: U | P t }),
  x = y <-> get x = get y.
Proof. split.
  - intros ->. reflexivity.
  - destruct x, y; simpl. intros ->. f_equal. apply proof_irrelevance. Qed.


(* Function type - considered normal setoid *)

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


(* Injective & Surjective *)
Definition injective `(f: U -> V): Prop :=
  forall x x': U, f x = f x' -> x = x'.

Definition surjective `(f: U -> V): Prop :=
  forall y: V, exists x: U, y = f x.

Definition bijective `(f: U -> V): Prop :=
  injective f /\ surjective f.


Lemma bi_unique_inv: forall `(f: U -> V) (y: V),
  bijective f -> exists ! x, y = f x.
Proof. intros * [I S].
  specialize (S y) as [x ->]. exists x. split; auto. Qed.

Lemma left_inv_then_inj: forall `(f: U -> V) (g: V -> U),
  (forall x, g (f x) = x) -> injective f.
Proof. intros ** x x' E. rewrite <- (H x), <- (H x'). f_equal. trivial. Qed.

Lemma right_inv_then_surj: forall `(f: U -> V) (g: V -> U),
  (forall y, f (g y) = y) -> surjective f.
Proof. intros ** y. exists (g y). easy. Qed.


(* Aid on unique existence *)
Lemma unique_by_uniqueness: forall U (P: U -> Prop) u,
  P u -> uniqueness P -> unique P u.
Proof. firstorder. Qed.


(*
  Not used
Fixpoint generalize_all (l: Tlist) (x: T): arrows l T :=
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
*)


(* The following are equivalent *)
Definition TFAE (l: list Prop) : Prop :=
  forall n m : nat, nth n l False -> nth m l True.

Fixpoint chain_impl (P: Prop) (l: list Prop): Prop :=
  match l with
  | Q :: l' => (P -> Q) /\ chain_impl Q l'
  | _ => True
  end.

Lemma tfae_by_chain: forall P (l: list Prop),
  chain_impl P l ->
  (nth (pred (length l)) l False -> P) -> TFAE (P :: l).
Proof.
  intros *. generalize dependent P.
  induction l as [| Q l'].
  - intros ? _ _ n m. destruct n. destruct m. trivial.
    + simpl. destruct m; trivial.
    + simpl. destruct n; contradiction.
  - intros ? [HF HC] HL n m.
    assert (IH: TFAE (Q :: l')). {
      apply IHl'. apply HC. simpl in HL.
      destruct l'; firstorder.
    }
    destruct n, m; trivial.
    + intros H0%HF. apply (IH 0 m). trivial.
    + intros H0%(IH n (length l')). apply HL.
      rewrite nth_indep with (d' := True). trivial. auto.
    + apply IH.
Qed.

Ltac tfae_chain := apply tfae_by_chain;
  unfold chain_impl, nth, length, pred; repeat apply conj; trivial.

Lemma tfae_then_any: forall (n m: nat) (l: list Prop),
  TFAE l -> nth n l False -> nth m l True.
Proof. firstorder. Qed.

