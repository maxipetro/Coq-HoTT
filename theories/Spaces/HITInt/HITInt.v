(** * The integers, defined as a HIT *)

(** Following "The integers as a higher inductive type" by Scoccola and Altenkirch, we define the integers as a higher inductive type.  Morally it is the free pointed type with a biinvertible self-map. *)

Require Import HoTT.Basics.
Require Import Types.Paths.
Require Import Spaces.Nat.Core.
Require Import Spaces.SInt.
Require Import Equiv.BiInv.

Set Universe Minimization ToSet.

Module Export IntHIT.
  Section IntHIT.

    (** Here we are modeling the HIT which has a point [zero_i] and a successor map [succ] which is a biinvertible equivalence.  [pred] and [succ_sect] are its left and right inverses. *)

    Private Inductive IntHIT : Type0 :=
    | zero_i : IntHIT
    | succ : IntHIT -> IntHIT
    | pred : IntHIT -> IntHIT
    | succ_sect : IntHIT -> IntHIT.

    Axiom succ_is_sect : forall (z : IntHIT), pred (succ z) = z.

    Axiom succ_is_retr : forall (z : IntHIT), succ (succ_sect z) = z.

    Context {P : IntHIT -> Type} (t0 : P zero_i) (e : forall z : IntHIT, P z -> P (succ z))
      (r : forall z : IntHIT, P z -> P (pred z)) (s : forall z : IntHIT, P z -> P (succ_sect z))
      (re : forall (z : IntHIT) (t : P z), succ_is_sect z # (r (succ z) (e z t)) = t)
      (es : forall (z : IntHIT) (t : P z), succ_is_retr z # (e (succ_sect z) (s z t)) = t).

    Fixpoint IntHIT_ind (x : IntHIT) : P x
      := match x with
      | zero_i => fun _ _ => t0
      | succ z => fun _ _ => e z (IntHIT_ind z)
      | pred z => fun _ _ => r z (IntHIT_ind z)
      | succ_sect z => fun _ _ => s z (IntHIT_ind z)
      end re es.
      (** We make sure that this is dependent on [re] and [es] as well. *)

    (** The beta principles for [IntHIT_ind] on [succ_is_sect] and [succ_is_retr]. *)
    Axiom IntHIT_ind_beta_succ_is_sect
      : forall (z: IntHIT), apD IntHIT_ind (succ_is_sect z) = re z (IntHIT_ind z).

    Axiom IntHIT_ind_beta_succ_is_retr
      : forall (z: IntHIT), apD IntHIT_ind (succ_is_retr z) = es z (IntHIT_ind z).

  End IntHIT.
End IntHIT.

(** Successor is biinvertible.  It follows from typeclass inference that it is an equivalence. *)
Instance isbiinv_IntHIT_succ : IsBiInv succ
  := Build_IsBiInv _ _ _ succ_sect pred succ_is_retr succ_is_sect.

Definition biinv_IntHIT_succ : BiInv IntHIT IntHIT
  := Build_BiInv _ _ _ _.

(** The predecessor is an equivalence on [IntHIT]. *)
Instance isequiv_IntHIT_pred : IsEquiv pred
  := isequiv_isbiinv_retr succ.

Definition IntHIT_ind_hprop {P : IntHIT -> Type} `{forall x, IsHProp (P x)}
  (t0 : P zero_i)
  (f : forall z : IntHIT, P z -> P (succ z))
  (g : forall z : IntHIT, P z -> P (pred z))
  : forall x, P x.
Proof.
  snapply (IntHIT_ind t0 f g).
  - intros z t.
    exact ((sect_retr_homotopic_isbiinv succ z)^ # (g z) t).
  - intros z t.
    rapply path_ishprop.
  - intros z t.
    rapply path_ishprop.
Defined.

Definition IntHIT_ind_hprop_iff {P : IntHIT -> Type} `{forall x, IsHProp (P x)}
  (t0 : P zero_i) (f : forall z : IntHIT, P z <-> P (succ z))
  : forall x, P x.
Proof.
  srapply (IntHIT_ind_hprop t0).
  - intro z.  exact (fst (f z)).
  - equiv_intro succ z.
    refine (_ o snd (f z)).
    exact (transport P (succ_is_sect z)^).
Defined.

(** The recursion principle. *)
Definition IntHIT_rec {P : Type} (t0 : P)
  (f : P -> P) (g1 : P -> P) (g2 : P -> P)
  (s : forall (t : P), g1 (f t) = t)
  (r : forall (t : P), f (g2 t) = t)
  : IntHIT -> P.
Proof.
  snapply (IntHIT_ind t0 (fun _ => f) (fun _ => g1) (fun _ => g2)).
  all: intros z t; cbn.
  all: lhs napply transport_const.
  - apply s.
  - apply r.
Defined.

(** This version of the recursion principle requires only a biinvertible map. *)
Definition IntHIT_rec_biinv {P : Type} (t0 : P) (f : P -> P) `{IsBiInv P P f}
  : IntHIT -> P
  := IntHIT_rec t0 f (retr_biinv f) (sect_biinv f) (eissect_biinv f) (eisretr_biinv f).

(** This version of the recursion principle requires only a quasiinverse rather than a biinvertible map. *)
(** TODO: decide whether we really need *four* variants of the recursion principle! *)
Definition IntHIT_rec_qinv {P : Type} (t0 : P) (f : P -> P) (g : P -> P)
  (s : forall (t : P), g (f t)= t) (r : forall (t : P), f (g t)= t)
  : IntHIT -> P
  := IntHIT_rec t0 f g g s r.

(** This verison of the recursion principle requires only a half-adjoint equivalence.  Since it is an Instance that biinvertible maps are equivalent to half-adjoint equivalences using type class search one could also use IntHIT_rec_biinv instead. *)
Definition IntHIT_rec_equiv {P : Type} (t0 : P) (f : P -> P) `{IsEquiv P P f}
  : IntHIT -> P
  := @IntHIT_rec_biinv P t0 f (isbiinv_isequiv _ _).

(** We define equivalence iteration. *)
Definition IntHIT_iter {A} (f : A -> A) `{!IsEquiv f} (n : IntHIT) (a0 : A) : A
  := IntHIT_rec_equiv a0 f n.

Definition IntHIT_rec_beta_succ_is_sect
  (P : Type)
  (t0 : P)
  (f : P -> P)
  (g1 : P -> P)
  (g2 : P -> P)
  (s : forall (t : P), g1 (f t) = t)
  (r : forall (t : P), f (g2 t) = t)
  (f':=IntHIT_rec t0 f g1 g2 s r)
  : forall z, ap f' (succ_is_sect z) = s (f' z).
Proof.
  intro z.
  unfold IntHIT_rec.
  refine (cancelL _ _ _ _).
  refine ((apD_const _ _)^ @ _).
  rapply IntHIT_ind_beta_succ_is_sect.
Defined.

Definition IntHIT_rec_beta_succ_is_retr
  (P: Type)
  (t0 : P)
  (f : P -> P)
  (g1 : P -> P)
  (g2 : P -> P)
  (s : forall (t : P), g1 (f t)= t)
  (r : forall (t : P), f (g2 t)= t)
  (f':=IntHIT_rec t0 f g1 g2 s r)
  : forall z, ap f' (succ_is_retr z) = r (f' z).
Proof.
  intro z.
  unfold IntHIT_rec.
  refine (cancelL _ _ _ _).
  refine ((apD_const _ _)^ @ _).
  rapply IntHIT_ind_beta_succ_is_retr.
Defined.

Section Uniqueness.

  Context {P : Type} {e: BiInv P P}.

  Local Definition s := sect_biinv e.
  Local Definition r := retr_biinv e.
  Local Definition re:= eissect_biinv e.
  Local Definition es := eisretr_biinv e.

  (** We prove a uniqueness principle expressing the universal property of the recursor, up to propositional equality. *)
  Definition uniquenessZ
    (t0 : P)
    (k: IntHIT -> P)
    (p0 : (k zero_i) = t0)
    (pf : forall (z : IntHIT), (e o k) z = (k o succ) z)
    (rec := IntHIT_rec t0 e r s re es)
    : forall (z : IntHIT), k z = rec z.
    Proof.
    snapply IntHIT_ind.
    - simpl.
      exact p0.
    - simpl.
      intros z H.
      apply (ap e) in H.
      exact ((pf z)^ @ H).
    - simpl.
      intros z H.
      apply (ap r) in H.
      exact ((biinv_compat_pr biinv_IntHIT_succ e k k pf z)^ @ H).
    - intros z H.
      apply (ap s) in H.
      exact ((biinv_compat_ps biinv_IntHIT_succ e k k pf z)^ @ H).
    - simpl.
      intros z t.
      rewrite transport_paths_FlFr.
      rewrite ap_pp.
      rewrite concat_p_pp.
      rewrite (inv_pp _ _)^.
      rewrite concat_p_pp.
      rewrite ap_V.
      rewrite (inv_pp _ _)^.
      rewrite concat_p_pp.
      rewrite (biinv_compat_pre biinv_IntHIT_succ e k k pf z)^.
      rewrite (concat_p_pp _ _ _)^.
      apply moveR_Vp.
      rewrite (ap_compose _ _ _)^.
      rewrite IntHIT_rec_beta_succ_is_sect.
      apply (concat_A1p (f := r o e)).
    - simpl.
      intros z t.
      rewrite transport_paths_FlFr.
      rewrite ap_pp.
      rewrite concat_p_pp.
      rewrite (inv_pp _ _)^.
      rewrite concat_p_pp.
      rewrite ap_V.
      rewrite (inv_pp _ _)^.
      rewrite concat_p_pp.
      rewrite (biinv_compat_pes biinv_IntHIT_succ e k k pf z)^.
      rewrite (concat_p_pp _ _ _)^.
      apply moveR_Vp.
      rewrite (ap_compose _ _ _)^.
      rewrite IntHIT_rec_beta_succ_is_retr.
      apply (concat_A1p (f := e o s)).
  Defined.

  (** The following uniqueness principle states that if two maps out of [IntHIT] commute with 0 and the successor, then they are equal. *)
  Definition uniquenessZ_two_fun_biinv
    (k1: IntHIT -> P)
    (k2: IntHIT -> P)
    (p0 : k1 zero_i = k2 zero_i)
    (pf1 : forall (z : IntHIT), (e o k1) z = (k1 o succ) z)
    (pf2 : forall (z : IntHIT), (e o k2) z = (k2 o succ) z)
    : forall (z : IntHIT), k1 z = k2 z.
  Proof.
    intro z.
    exact ((uniquenessZ (k2 zero_i) k1 p0 pf1 z)
    @ (uniquenessZ (k2 zero_i) k2 idpath pf2 z)^).
  Defined.

End Uniqueness.

(** The same uniqueness principle but for half-adjoint equivalences. *)
Definition uniquenessZ_two_fun_equiv
  {P : Type}
  (f : P -> P)
  {e': IsEquiv f}
  (k1: IntHIT -> P)
  (k2: IntHIT -> P)
  (p0 : k1 zero_i = k2 zero_i)
  (pf1 : forall (z : IntHIT), (f o k1) z = (k1 o succ) z)
  (pf2 : forall (z : IntHIT), (f o k2) z = (k2 o succ) z)
  : forall (z : IntHIT), k1 z = k2 z
  := uniquenessZ_two_fun_biinv (e := Build_BiInv P P _ (isbiinv_isequiv f e')) k1 k2 p0 pf1 pf2.

(** Next we prove that [IntHIT] is equivalent to [SInt]. *)

Section IntHITEquiv.

  Definition IntHITtoIntIT : IntHIT -> SInt.
  Proof.
    srapply IntHIT_rec.
    - exact zero.
    - exact int_succ.
    - exact int_pred.
    - exact int_pred.
    - exact int_succ_pred.
    - exact int_pred_succ.
  Defined.

  Definition IntITtoIntHIT (z : SInt) : IntHIT.
  Proof.
    induction z.
    - exact zero_i.
    - exact (succ IHz).
    - exact (pred IHz).
  Defined.

  Definition IntITtoIntHIT_is_rinv (z : SInt)
    : (IntHITtoIntIT o IntITtoIntHIT) z = z.
  Proof.
    induction z as [|[|n] IHz|[|n] IHz].
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - apply (ap int_succ) in IHz.
      apply IHz.
    - simpl.
      reflexivity.
    - simpl.
      apply (ap int_pred) in IHz.
      apply IHz.
  Defined.

  Definition IntITtoIntHIT_comp_succ (z: SInt)
    : succ (IntITtoIntHIT z) = IntITtoIntHIT (int_succ z).
  Proof.
    simpl.
    induction z as [|[|n] IHz|[|n] IHz].
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - simpl.
      exact (retr_is_sect_isbiinv succ zero_i).
    - simpl.
      exact (retr_is_sect_isbiinv succ _).
  Defined.

  Definition IntITtoIntHIT_comp_succ' (z: IntHIT)
    : succ (IntITtoIntHIT (IntHITtoIntIT z)) = IntITtoIntHIT (IntHITtoIntIT (succ z)).
  Proof.
    simpl.
    exact ((IntITtoIntHIT_comp_succ o IntHITtoIntIT) z).
  Defined.

  Definition IntITtoIntHIT_is_linv (z : IntHIT)
    : (IntITtoIntHIT o IntHITtoIntIT) z = z.
  Proof.
    exact (((uniquenessZ (P := IntHIT) (e := biinv_IntHIT_succ) zero_i (IntITtoIntHIT o IntHITtoIntIT) idpath IntITtoIntHIT_comp_succ') z)
    @ ((uniquenessZ (P := IntHIT) (e := biinv_IntHIT_succ) zero_i idmap idpath (fun x => idpath)) z)^).
  Defined.

  (** [IntITtoIntHIT] is biinvertible.  It follows from typeclass inference that it is an equivalence and that [SInt] and [IntHIT] are equivalent. *)
  Global Instance isbiinv_IntITtoIntHIT
    : IsBiInv IntITtoIntHIT
    := Build_IsBiInv _ _ _ _ _ IntITtoIntHIT_is_linv IntITtoIntHIT_is_rinv.

  (** Since [SInt] is a set, therefore also [IntHIT] is a set. *)
  #[export] Instance ishset_IntHIT
    : IsHSet IntHIT
    := istrunc_isequiv_istrunc SInt _.

  (** We sometimes want to treat the integers as a pointed type with basepoint given by 0. *)
  #[export] Instance ispointed_IntHIT : IsPointed IntHIT := zero_i.

End IntHITEquiv.

(** * Integer Arithmetic using [IntHIT] *)

Section IntegerArithmetic.

  Declare Scope IntHIT_scope.
  Delimit Scope IntHIT_scope with IntHIT.
  Local Open Scope IntHIT_scope.

  Notation "z .+1" := (succ z) : IntHIT_scope.
  Notation "z .-1" := (pred z) : IntHIT_scope.

  (** We define negation by recursion.  Negation is defined at this early stage because it will be used in parsing numerals. *)
  Definition IntHIT_neg (x : IntHIT) : IntHIT
    := IntHIT_rec_equiv zero_i pred x.

  Notation "- x" := (IntHIT_neg x) : IntHIT_scope.

  (** We define addition by recursion on the first argument. *)
  Definition IntHIT_add (x y : IntHIT) : IntHIT
    := IntHIT_rec_equiv y succ x.

  (** We can convert a [nat] to an [IntHIT] by mapping [0] to [zero] and [S n] to [succ n].  Various operations on [nat] are preserved by this function. See the section on conversion functions starting with [int_nat_succ]. *)
  Definition IntHIT_of_nat (n : nat) : IntHIT
    := nat_iter n succ zero_i.

  (** Printing *)
  (** Here we rely for now on the 'old' integers. This can be maybe improved in the future. *)
  Definition IntHIT_to_number_int : IntHIT -> Numeral.int := int_to_number_int o IntHITtoIntIT.

  (** Parsing *)
  Definition IntHIT_of_number_int (d : Numeral.int) :=
    match d with
    | Numeral.IntDec (Decimal.Pos d) => IntHIT_of_nat (Nat.of_uint d)
    | Numeral.IntDec (Decimal.Neg d) => IntHIT_neg (IntHIT_of_nat (Nat.of_uint d))
    | Numeral.IntHex (Hexadecimal.Pos u) => IntHIT_of_nat (Nat.of_hex_uint u)
    | Numeral.IntHex (Hexadecimal.Neg u) => IntHIT_neg (IntHIT_of_nat (Nat.of_hex_uint u))
    end.

  Number Notation IntHIT IntHIT_of_number_int IntHIT_to_number_int : IntHIT_scope.

  (** The following function reduces an integer expression by cancelling succesive successor and predecessor terms. *)
  Definition IntHIT_reduce := IntITtoIntHIT o IntHITtoIntIT.

  (** ** Properties of Operations *)

  (** Negation is involutive. *)
  Definition IntHIT_neg_neg (x: IntHIT): - - x = x.
  Proof.
    revert x.
    by srapply (uniquenessZ_two_fun_equiv succ).
  Defined.

  (* * Negation is an equivalence. *)
  #[export] Instance isequiv_int_neg : IsEquiv IntHIT_neg.
  Proof.
    snapply (isequiv_adjointify IntHIT_neg IntHIT_neg).
    1,2: napply IntHIT_neg_neg.
  Defined.

  (** Negation is injective. *)
  Definition isinj_IntHIT_neg (x y : IntHIT) : - x = - y -> x = y
    := equiv_inj IntHIT_neg.

  (** The negation of a successor is the predecessor of the negation. *)
  Definition IntHIT_neg_succ (x : IntHIT) : - succ x = pred (-x)
    := idpath.

  (** The negation of a predecessor is the successor of the negation. *)
  Definition IntHIT_neg_pred (x : IntHIT) : - pred x = succ (- x)
    := idpath.

  (** *** Addition *)

  Infix "+" := IntHIT_add : IntHIT_scope.
  Infix "-" := (fun x y => x + -y) : IntHIT_scope.

  (** Integer addition with zero on the left is the identity by definition. *)
  Definition IntHIT_add_0_l (x : IntHIT) : 0 + x = x
    := idpath.

  (** Integer addition with zero on the right is the identity. *)
  Definition IntHIT_add_0_r (x : IntHIT) : x + 0 = x.
  Proof.
    revert x.
    by srapply (uniquenessZ_two_fun_equiv succ).
  Defined.

  (** Adding a successor on the left is the successor of the sum. *)
  Definition IntHIT_add_succ_l (x y : IntHIT) : (succ x) + y = succ (x + y)
    := idpath.

  (** Adding a predecessor on the left is the predecessor of the sum. *)
  Definition IntHIT_add_pred_l (x y : IntHIT) : (pred x) + y = pred (x + y)
    := idpath.

  (** Adding a successor on the right is the successor of the sum. *)
  Definition IntHIT_add_succ_r (x y : IntHIT) : x + (succ y) = succ (x + y).
  Proof.
    revert x.
    by srapply (uniquenessZ_two_fun_equiv succ).
  Defined.

  (** Adding a predecessor on the right is the predecessor of the sum. *)
  Definition IntHIT_add_pred_r (x y : IntHIT) : x + (pred y) = pred (x + y).
  Proof.
    revert x.
    srapply (uniquenessZ_two_fun_equiv succ); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro z.
      simpl.
      rewrite succ_is_sect.
      by rewrite (fun z => (retr_is_sect_isbiinv succ z)^).
  Defined.

  (** Integer addition with 1 on the left is the successor. *)
  Definition IntHIT_add_1_l (x : IntHIT) : 1 + x = succ x
    := idpath.

  (** Integer addition with 1 on the right is the successor. *)
  Definition IntHIT_add_1_r (x : IntHIT) : x + 1 = succ x.
  Proof.
    revert x.
    by srapply (uniquenessZ_two_fun_equiv succ).
  Defined.

  (** Integer addition is commutative. *)
  Definition IntHIT_add_comm (x y : IntHIT) : x + y = y + x.
  Proof.
    revert x.
    srapply (uniquenessZ_two_fun_equiv succ); cbn beta.
    - by rewrite IntHIT_add_0_r.
    - reflexivity.
    - intro z.
      by rewrite IntHIT_add_succ_r.
  Defined.

  (** Integer addition is associative. *)
  Definition IntHIT_add_assoc (x y z : IntHIT) : x + (y + z) = x + y + z.
  Proof.
    revert x.
    by srapply (uniquenessZ_two_fun_equiv succ).
  Defined.

  (** Negation is a left inverse with respect to integer addition. *)
  Definition IntHIT_add_neg_l (x : IntHIT) : - x + x = 0.
  Proof.
    revert x.
    srapply (uniquenessZ_two_fun_equiv idmap); cbn beta.
    - reflexivity.
    - simpl.
      intro s.
      rewrite IntHIT_add_succ_r.
      rewrite succ_is_sect.
      reflexivity.
    - reflexivity.
  Defined.

  (** Negation is a right inverse with respect to integer addition. *)
  Definition IntHIT_add_neg_r (x : IntHIT) : x - x = 0.
  Proof.
    unfold "-"; by rewrite IntHIT_add_comm, IntHIT_add_neg_l.
  Defined.

  (** Negation distributes over addition. *)
  Definition IntHIT_neg_add (x y : IntHIT) : - (x + y) = - x - y.
  Proof.
    revert x.
    by srapply (uniquenessZ_two_fun_equiv pred).
  Defined.

  (** Addition is an equivalence with first argument fixed. *)
  #[export] Instance isequiv_IntHIT_add_l (x : IntHIT): IsEquiv (IntHIT_add x).
  Proof.
    srapply (isequiv_adjointify (IntHIT_add x) (IntHIT_add (-x))).
    - simpl.
      intro y.
      rewrite IntHIT_add_assoc.
      by rewrite IntHIT_add_neg_r.
    - simpl.
      intro y.
      rewrite IntHIT_add_assoc.
      by rewrite IntHIT_add_neg_l.
  Defined.

  (** Addition is an equivalence with second argument fixed. *)
  #[export] Instance isequiv_IntHIT_add_r (y : IntHIT): IsEquiv (fun x => IntHIT_add x y).
  Proof.
    snapply (isequiv_adjointify (fun x => IntHIT_add x y) (fun x => IntHIT_add x (-y))).
    - simpl.
      intro x.
      rewrite <- IntHIT_add_assoc.
      rewrite IntHIT_add_neg_l.
      by rewrite IntHIT_add_0_r.
    - simpl.
      intro x.
      rewrite <- IntHIT_add_assoc.
      rewrite IntHIT_add_neg_r.
      by rewrite IntHIT_add_0_r.
  Defined.

  (** *** Multiplication *)

  (** We define multiplication by recursion on the first argument.  We can only define it at this stage as it depends on the proof that addition is an equivalence. *)
  Definition IntHIT_mul (x y : IntHIT) : IntHIT
    := IntHIT_iter (fun z => IntHIT_add z y) x 0.

  Infix "*" := IntHIT_mul : IntHIT_scope.

  (** Multiplication with a successor on the left is the sum of the multplication without the successor and the multiplicand which was not a successor. *)
  Definition IntHIT_mul_succ_l (x y : IntHIT) : (succ x) * y = x * y + y
    := idpath.

  (** Similarly, multiplication with a predecessor on the left is the sum of the multiplication without the predecessor and the negation of the multiplicand which was not a predecessor. *)
  Definition IntHIT_mul_pred_l (x y : IntHIT) : (pred x) * y = x * y - y
    := idpath.

  (** Integer multiplication with zero on the left is zero by definition. *)
  Definition IntHIT_mul_0_l (x : IntHIT) : 0 * x = 0
    := idpath.

  (** Integer multiplication with zero on the right is zero. *)
  Definition IntHIT_mul_0_r (x : IntHIT) : x * 0 = 0.
  Proof.
    revert x.
    rapply (uniquenessZ_two_fun_equiv idmap); cbn beta.
    - reflexivity.
    - simpl.
      intro z.
      by rewrite IntHIT_add_0_r.
    - reflexivity.
  Defined.

  (** Integer multiplication with one on the left is the identity. *)
  Definition IntHIT_mul_1_l (x : IntHIT) : 1 * x = x
    := idpath.

  (** Integer multiplication with one on the right is the identity. *)
  Definition IntHIT_mul_1_r (x : IntHIT) : x * 1 = x.
  Proof.
    revert x.
    rapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x 1)); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro z.
      by rewrite IntHIT_add_1_r.
  Defined.

  (** Integer multiplication with -1 on the left is negation. *)
  Definition IntHIT_mul_neg1_l (x : IntHIT) : (-1) * x = - x
    := idpath.

  (** Multiplying with a negation on the left is the same as negating the product. *)
  Definition IntHIT_mul_neg_l (x y : IntHIT) : - x * y = - (x * y).
  Proof.
    revert x.
    rapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x (-y))); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro x; simpl.
      rewrite IntHIT_neg_add.
      reflexivity.
  Defined.

  (** Multiplying with a successor on the right is the sum of the multiplication without the successor and the product of the multiplicand which was not a successor and the multiplicand. *)
  Definition IntHIT_mul_succ_r (x y : IntHIT) : x * (succ y) = x + x * y.
  Proof.
    revert x.
    rapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x (succ y))); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro z; simpl.
      rewrite IntHIT_add_succ_r.
      by rewrite IntHIT_add_assoc.
  Defined.

  (** Multiplying with a predecessor on the right is the sum of the multiplication without the predecessor and the product of the multiplicand which was not a predecessor and the negation of the multiplicand which was not a predecessor. *)
  Definition IntHIT_mul_pred_r (x y : IntHIT) : x * (pred y) = x * y - x.
  Proof.
    revert x.
    rapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x (pred y))); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro z.
      rewrite IntHIT_mul_succ_l.
      rewrite <- IntHIT_add_assoc.
      rewrite (IntHIT_add_comm (-z) _).
      rewrite IntHIT_add_pred_l.
      rewrite <- IntHIT_add_assoc.
      rewrite IntHIT_neg_succ.
      by rewrite (IntHIT_add_pred_r y _).
  Defined.

  (** Integer multiplication is commutative. *)
  Definition IntHIT_mul_comm (x y : IntHIT) : x * y = y * x.
  Proof.
    revert x.
    srapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x y)); cbn beta.
    - symmetry; apply IntHIT_mul_0_r.
    - reflexivity.
    - intro z.
      rewrite IntHIT_add_comm.
      symmetry; apply IntHIT_mul_succ_r.
  Defined.

  (** Multiplying with a negation on the right is the same as negating the product. *)
  Definition IntHIT_mul_neg_r (x y : IntHIT) : x * - y = - (x * y).
  Proof.
    rewrite !(IntHIT_mul_comm x).
    apply IntHIT_mul_neg_l.
  Defined.

  (** Multiplication distributes over addition on the left. *)
  Definition IntHIT_dist_l (x y z : IntHIT) : x * (y + z) = x * y + x * z.
  Proof.
    revert x.
    srapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x (y + z))); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro x.
      simpl.
      rewrite <- (IntHIT_add_assoc (x*y) y).
      rewrite (IntHIT_add_comm y (x*z + z)).
      rewrite <- (IntHIT_add_assoc _ z y).
      rewrite (IntHIT_add_comm z y).
      by rewrite (IntHIT_add_assoc (x*y) _ _).
  Defined.

  (** Multiplication distributes over addition on the right. *)
  Definition IntHIT_dist_r (x y z : IntHIT) : (x + y) * z = x * z + y * z.
  Proof.
    by rewrite IntHIT_mul_comm, IntHIT_dist_l, !(IntHIT_mul_comm z).
  Defined.

  (** Multiplication is associative. *)
  Definition IntHIT_mul_assoc (x y z : IntHIT) : x * (y * z) = x * y * z.
  Proof.
    revert x.
    srapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x (y * z))); cbn beta.
    - reflexivity.
    - reflexivity.
    - simpl.
      intro x.
      by rewrite IntHIT_dist_r.
  Defined.

  (** This is a shorter proof of [IntITtoIntHIT_is_linv], but it requires that we already know that [IntHIT] is as set.  This might be useful in the future, if we can show that [IntHIT] a set independently of its equivalence to [SInt]. *)
  Definition IntITtoIntHIT_is_linv' (z : IntHIT)
  : (IntITtoIntHIT o IntHITtoIntIT) z = z.
  Proof.
    srapply (uniquenessZ_two_fun_equiv succ).
    - reflexivity.
    - simpl.
      exact IntITtoIntHIT_comp_succ'.
    - reflexivity.
  Defined.

End IntegerArithmetic.
