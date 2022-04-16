From Mtac2 Require Export Mtac2.
Export M M.notations.

From Practice Require Import Base Evaluable.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.


Notation "! t" := ltac: (mrun t) (at level 200).


(* Equality check - evaluates second argument *)
Definition meqb U (x y: U): M bool :=
  mmatch y with
  | x => ret true | _ => ret false
  end.

(*
  Finds a value x in sequence l satisfying mtac predicate p.
  Returns None if not found.
*)
Definition mfind `(p: U -> M bool): list U -> M (option U) :=
  fix mfind l :=
    match l with
    | [::] => ret None
    | x :: l' =>
      mif p x
      then ret (Some x)
      else mfind l'
    end.

Local Example mfind_ex1: (! mfind [fun x => meqb (S x) 3] [:: 1; 2; 4]) = Some 2 :=
  erefl.
Local Example mfind_ex2: (! mfind [fun x => meqb (S x) 4] [:: 1; 2; 4]) = None :=
  erefl.

(* Filters a sequence l with mtac predicate p. *)
Definition mfilter `(p: U -> M bool): list U -> M (list U) :=
  fix mfilter l :=
    match l with
    | [::] => ret [::]
    | x :: l' =>
        m <- mfilter l'
      ; mif p x then ret (x :: m) else ret m
    end.

Local Example mfilter_ex1:
  (! mfilter [fun n => ret (n > 3)] [:: 1; 2; 4]) = [:: 4] := erefl.
Local Example mfilter_ex2:
  (! mfilter [fun n => orb <$> meqb n 4 <*> meqb n 1] [:: 1; 2; 4]) = [:: 1; 4] := erefl.

  
(* Remove duplicates in the list. *)
Definition mrmdup U: list U -> M (list U) :=
  fix mrmdup l :=
    match l with
    | [::] => ret [::]
    | x :: l' =>
        m <- mrmdup l'
      ; mif (isSome <$> mfind (meqb x) m) then ret m else ret (x :: m)
    end.

Local Example mrmdup_ex1: (! mrmdup [:: 1; S 2; 3; 2]) = [:: 1; 3; 2] :=
  erefl.
Local Example mrmdup_ex2: (! mrmdup [:: 4; 1; 3]) = [:: 4; 1; 3] :=
  erefl.



Definition NoInvert n T (W: n.-tuple T) (a: T): Exception := ltac: (reflexivity).


Import EqNotations.

(*
  Finds a mapping "f: 'I_m -> 'I_n" which maps index
  s.t. "tnth V =1 tnth W \o f".
*)
Program Definition mtupmap `(V: m.-tuple T) `(W: n.-tuple T): M ('I_m -> 'I_n) :=
  (* Find m: seq 'I_n with l = map (tnth W) m  *)
  let fix revMap l :=
    match l with
    | [::] => ret [::]
    | a :: l' =>
        m <- revMap l'
      ; ox <- mfind [fun i => meqb a (tnth W i)] (enumOrd n)
      ; mmatch ox with
        | [?x] Some x => ret (x :: m)
        | None => raise (NoInvert W a)
        end
      end
  in tf <- revMap (val V);
    if n > 0 is true
    then ret (fun i => nth (@Ordinal n 0 _) tf (val i))
    else raise Exceptions.NotFound.

(* ^ Simply to make compiler happy *)
(* TODO construct it out of tuple *)

Local Example mtupmap_ex1:
  map (! mtupmap [tuple 3; 1; 4] [tuple 1; 2; 3; 4; 5]) (enumOrd 3) =
  [:: 5.-ord 2; 5.-ord 0; 5.-ord 3] := erefl.

Local Example mtupmap_ex2:
  map (! mtupmap [tuple 3; 1; 4] [tuple 2; 4; 5; 3; 1]) (enumOrd 3) =
  [:: 5.-ord 3; 5.-ord 4; 5.-ord 1] := erefl.

