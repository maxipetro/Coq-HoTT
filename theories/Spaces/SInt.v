Require Import Basics.Overture Basics.Nat Basics.Tactics Basics.Decidable.
Require Basics.Numerals.Decimal.
Require Import Spaces.Nat.Core. (* TODO: Can we remove this?  Currently used for [nat_pred] below. *)

Unset Elimination Schemes.
Set Universe Minimization ToSet.

(** * The signed integers *)

(** In this file, we give a simple inductive type that represents the integers.  It is straightforward to show that this type has decidable equality and is therefore a set, and it is also straightforward to print and parse integers using this type.  However, we only use it for these purposes, and treat the HIT integers as our main definition of the integers, since they have an induction principle with better computational behaviour. *)

(** ** Definition *)

(** We define the signed integers as two copies of [nat] stuck together around a [zero]. *)
Inductive SInt : Type0 :=
| negS : nat -> SInt
| zero : SInt
| posS : nat -> SInt.

(** We can convert a [nat] to an [SInt] by mapping [0] to [zero] and [S n] to [posS n]. *)
Definition int_of_nat (n : nat) :=
  match n with
  | O => zero
  | S n => posS n
  end.

Coercion int_of_nat : nat >-> SInt.

(** ** Number Notations *)

(** Here we define some printing and parsing functions that convert the integers between numeral representations so that we can use notations such as [123] for [posS 122] and [-123] for [negS 122]. *)

(** Printing *)
Definition int_to_number_int (n : SInt) : Numeral.int :=
  match n with
  | posS n => Numeral.IntDec (Decimal.Pos (Nat.to_uint (S n)))
  | zero => Numeral.IntDec (Decimal.Pos (Nat.to_uint 0))
  | negS n => Numeral.IntDec (Decimal.Neg (Nat.to_uint (S n)))
  end.

(** Parsing *)
Definition int_of_number_int (d : Numeral.int) :=
  match d with
  | Numeral.IntDec (Decimal.Pos d) => int_of_nat (Nat.of_uint d)
  | Numeral.IntDec (Decimal.Neg d) => negS (nat_pred (Nat.of_uint d))
  | Numeral.IntHex (Hexadecimal.Pos u) => int_of_nat (Nat.of_hex_uint u)
  | Numeral.IntHex (Hexadecimal.Neg u) => negS (nat_pred (Nat.of_hex_uint u))
  end.

(** ** Successor, Predecessor and Negation *)

Definition int_succ (n : SInt) : SInt :=
  match n with
  | posS n => posS (S n)
  | zero => posS 0
  | negS 0 => zero
  | negS (S n) => negS n
  end.

Definition int_pred (n : SInt) : SInt :=
  match n with
  | posS (S n) => posS n
  | posS 0 => zero 
  | zero => negS 0
  | negS n => negS (S n)
  end.

Definition int_neg@{} (x : SInt) : SInt :=
  match x with
  | posS x => negS x
  | zero => zero
  | negS x => posS x
  end.

(** The successor of a predecessor is the identity. *)
Definition int_pred_succ@{} (x : SInt) : int_succ (int_pred x) = x.
Proof.
  by destruct x as [ | | []].
Defined.

(** The predecessor of a successor is the identity. *)
Definition int_succ_pred@{} (x : SInt) : int_pred (int_succ x) = x.
Proof.
  by destruct x as [[] | | ].
Defined.

(** ** Decidable Equality *)

(** The integers have decidable equality. *)
Global Instance decidable_paths_int@{} : DecidablePaths SInt.
Proof.
  intros [x | | x] [y | | y].
  2-4,6-8: right; intros; discriminate.
  2: by left.
  1,2: napply decidable_iff.
  1,3: split.
  1,3: napply ap.
  1,2: intros H; by injection H.
  1,2: exact _.
Defined.

(** By Hedberg's theorem, we have that the integers are a set. *)
Global Instance ishset_int@{} : IsHSet SInt := _.

(** ** Integer induction *)

(** The induction principle for signed integers is similar to the induction principle for natural numbers. However we have two induction hypotheses going in either direction starting from [0]. *)
(** TODO: This is slightly altered compared to Int.v, and I don't know which was is better. *)
(** TODO: This is used only in HITInt.v.  It may be possible to completely avoid it, which would then let us drop [int_of_nat] as well. *)
Definition SInt_ind@{i} (P : SInt -> Type@{i})
  (H0 : P zero)
  (HP : forall n : nat, P n -> P (posS n))
  (HN : forall n : nat, P (int_neg n) -> P (negS n))
  : forall x, P x.
Proof.
  intros [x | | x].
  - induction x as [|x IHx].
    + apply (HN 0%nat), H0.
    + apply (HN x.+1%nat), IHx.
  - exact H0.
  - induction x as [|x IHx].
    * apply (HP 0%nat), H0.
    * apply (HP x.+1%nat), IHx.
Defined.

(** We record these so that they can be used with the [induction] tactic. *)
Definition SInt_rect := SInt_ind.
Definition SInt_rec := SInt_ind.
