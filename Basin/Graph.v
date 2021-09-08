(* ----------------------------------------------------------------- *)
(*                      Evaluable Finite Graphs                      *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Base.
From mathcomp Require Export fintype path fingraph tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.


(* Computable definition of ord_tuple *)

Definition compIdP (b: bool): reflect b b :=
  if b
  then ReflectT true is_true_true
  else ReflectF false not_false_is_true.
Arguments compIdP {b}.

Section SubType.

Variable T: Type.
Variable P: pred T.
Variable sT: subType P.

Definition sembed x :=
  if compIdP is ReflectT Px then Some (Sub (sT := sT) x Px) else None.

Property sembedP x: insub_spec x (sembed x).
Proof.
  rewrite /sembed.
  case: {-}_ /compIdP; by [left; rewrite ?SubK | right; apply/negP].
Qed.

Property sembed_insub: sembed =1 insub.
Proof.
  move=> x. case: sembedP=> [/SubP[y Py] _ <- | /negPf nPx].
  rewrite SubK insubT //. rewrite insubF //.
Qed.

End SubType.

Arguments sembed {T P sT} x.


Definition enumOrd n: seq (ordinal n) := pmap sembed (iota 0 n).

Property enumOrd_enum n: enumOrd n = enum 'I_n.
Proof. rewrite enumT unlock /= /enumOrd /ord_enum. apply/eq_pmap /sembed_insub. Qed.

Lemma filter_enumOrd_enum n (A: {pred 'I_n}): filter A (enumOrd n) = enum A.
Proof. rewrite enumOrd_enum enumT //. Qed.



Program Definition tupleOrd n: (n.-tuple 'I_n) := @Tuple _ _ (enumOrd n) _.
Next Obligation. rewrite enumOrd_enum. apply/eqP/size_enum_ord. Qed.

Property tupleOrd_ord_tuple n: tupleOrd n = ord_tuple n.
Proof. apply /val_inj. simpl. apply/enumOrd_enum. Qed.


Definition tupleOf `(f: 'I_n -> T) := map_tuple f (tupleOrd n).

Property tupleOf_mktuple `(f: 'I_n -> T): tupleOf f = mktuple f.
Proof. apply /val_inj. rewrite /= enumOrd_enum //. Qed.

Property tupleOf_tnth `(f: 'I_n -> T): tnth (tupleOf f) =1 f.
Proof. move=> i. rewrite tupleOf_mktuple tnth_mktuple //. Qed.

Notation "n '.-ord' i" := (Ordinal (n:=n) (m:=i) is_true_true) (at level 10).


Lemma tnth_zip `(t: n.-tuple T) `(u: n.-tuple U) i:
  tnth (zip_tuple t u) i = (tnth t i, tnth u i).
Proof.
  rewrite /tnth. move: (tnth_default (zip_tuple t u))=> [d e].
  rewrite nth_zip ?size_tuple // -!tnth_nth //.
Qed.


Section Graph.
Variable n: nat.

Definition graph := n.-tuple (seq 'I_n).

Definition grrel (G: graph) := grel (tnth G).
Definition relgraph (r: rel 'I_n) :=
  tupleOf [fun i => filter (r i) (enumOrd n)].

Property relgraph_rgraph r: relgraph r = tupleOf (rgraph r).
Proof.
  rewrite /relgraph !tupleOf_mktuple.
  apply/eq_mktuple=> i /=. rewrite enumOrd_enum enumT //.
Qed.

Property relgraphK r: grrel (relgraph r) =2 r.
Proof.
  rewrite relgraph_rgraph /grrel /grel.
  move=> i j /=. rewrite tupleOf_tnth.
  rewrite -rgraphK //.
Qed.


Definition grwf (G: graph): graph :=
  relgraph (grrel G).


(* Assume well-formed graph *)
Definition grincl (G K: graph) :=
  all [pred gk | subseq gk.1 gk.2] (zip_tuple G K).

Lemma grincl_rel G K i j: grincl G K -> grrel G i j -> grrel K i j.
Proof.
  move=> /all_tnthP /(_ i) /=.
  rewrite tnth_zip /=. by move/mem_subseq /(_ j).
Qed.



(* Graph addition *)
Definition gradd (G K: graph) :=
  grwf (map_tuple [fun gk => gk.1 ++ gk.2] (zip_tuple G K)).

Property graddK G K: grrel (gradd G K) =2 [rel i j | grrel G i j || grrel K i j].
Proof.
  move=> i j. rewrite relgraphK /=.
  rewrite tnth_map tnth_zip /=. apply/mem_cat.
Qed.


Definition transCl (G: graph): graph :=
  tupleOf (dfs (tnth G) n [::]).

Lemma transClP G x y:
  reflect (exists2 p, path (grrel G) x p & y = last x p)
  (grrel (transCl G) x y).
Proof.
  rewrite /grrel /transCl /=.
  rewrite tupleOf_mktuple tnth_mktuple.
  have := (@dfsP _ (tnth G) x y). by rewrite card_ord.
Qed.

Lemma transCl_trans G: transitive (grrel (transCl G)).
Proof.
  move=> x y z /transClP[p ep ->] /transClP[q eq ->]. apply/transClP.
  exists (p ++ q); by [rewrite cat_path ep eq | rewrite last_cat].
Qed.

Lemma transCl_conn0 G x: grrel (transCl G) x x.
Proof. apply/transClP. by exists [::]. Qed.

Lemma transCl_conn1 G x y: grrel G x y -> grrel (transCl G) x y.
Proof. move=> /= H. apply/transClP. exists [:: y]; rewrite /= ?H //. Qed.

End Graph.


Section Image.
Variable m n: nat.
Variable f: 'I_m -> 'I_n.

Definition graphpre (G: graph n): graph m :=
  tupleOf (fun a => filter [preim f of tnth G (f a)] (enumOrd m)).

Definition graphim (G: graph m): graph n :=
  tupleOf (fun x => [seq f b |
    a <- (filter [preim f of pred1 x] (enumOrd m)),
    b <- tnth G a
  ]).


Section InjImage.
Hypothesis If: injective f.

(* TODO Later move to more general *)
Lemma preim_pred1 a: [preim f of pred1 (f a)] =1 pred1 a.
Proof. move=> i /=. by apply /inj_eq. Qed.

Lemma graph_im_pre G: graphpre (graphim G) = grwf G.
Proof.
  apply/eq_from_tnth=> a. rewrite !tupleOf_tnth.
  apply/eq_filter=> b /=.
  under eq_filter=> i do rewrite preim_pred1.
  rewrite filter_enumOrd_enum enum1 /=.
  rewrite cats0. by apply/mem_map.
Qed.

End InjImage.

End Image.


