Require Import HoTT.Basics Types.Prod Types.Equiv Types.Sigma Types.Universe.

Local Open Scope path_scope.
Generalizable Variables A B f.

(** * Bi-invertible maps *)

(** A map is "bi-invertible" if it has both a section and a retraction, not necessarily the same.  This definition of equivalence was proposed by Andre Joyal. *)

Class IsBiInv {A B : Type} (e : A -> B) := {
  sect_biinv : B -> A ;
  retr_biinv : B -> A ;
  eisretr_biinv : e o sect_biinv == idmap ;
  eissect_biinv : retr_biinv o e == idmap ;
}.

Record BiInv A B := {
  biinv_fun :> A -> B ;
  biinv_isbiinv :> IsBiInv biinv_fun
}.

Arguments sect_biinv {A B}%_type_scope e%_function_scope {_} _.
Arguments retr_biinv {A B}%_type_scope e%_function_scope {_} _.
Arguments eisretr_biinv {A B}%_type_scope e%_function_scope {_} _.
Arguments eissect_biinv {A B}%_type_scope e%_function_scope {_} _.

(** If [e] is bi-invertible, then the retraction and the section of [e] are equal. *)
Definition sect_retr_homotopic_isbiinv {A B : Type} (f : A -> B) `{bi : !IsBiInv f}
  : sect_biinv f == retr_biinv f.
Proof.
  revert bi.
  intros [h g r s].
  exact (fun y => (s (h y))^ @ ap g (r y)).
Defined.

Definition retr_is_sect_isbiinv {A B : Type} (f : A -> B) `{bi : !IsBiInv f}
  : f o retr_biinv f == idmap.
Proof.
  intro z.
  lhs_V napply (ap f (sect_retr_homotopic_isbiinv f z)).
  apply eisretr_biinv.
Defined.

Definition sect_is_retr_isbiinv {A B : Type} (f : A -> B) `{bi : !IsBiInv f}
  : sect_biinv f o f == idmap.
Proof.
  intro z.
  lhs napply sect_retr_homotopic_isbiinv.
  apply eissect_biinv.
Defined.

(** The record is equivalent to a product type. This is used below in a 'product of contractible types is contractible' argument. *)
Definition prod_isbiinv (A B : Type) `{f: A -> B}
  : {g : B -> A & g o f == idmap} * {h : B -> A & f o h == idmap} <~> IsBiInv f.
Proof.
  make_equiv.
Defined.

Existing Instance biinv_isbiinv.

Definition issig_BiInv (A B : Type)
  : {f : A -> B & IsBiInv f} <~> BiInv A B.
Proof.
  issig.
Defined.

(** From a bi-invertible map, we can construct a half-adjoint equivalence in two ways. Here we take the inverse to be the retraction. *)
Global Instance isequiv_isbiinv {A B : Type} (f : A -> B) `{bi : !IsBiInv f} : IsEquiv f.
Proof.
  revert bi.
  intros [h g r s].
  exact (isequiv_adjointify f g
    (fun x => ap f (ap g (r x)^ @ s (h x)) @ r x)
    s).
Defined.

Global Instance isequiv_isbiinv_retr {A B : Type} (f : A -> B) `{bi : !IsBiInv f} : IsEquiv (retr_biinv f)
  := isequiv_inverse f.

(** Here we take the inverse to be the section. *)
Definition isequiv_isbiinv' {A B : Type} (f : A -> B) `{bi : !IsBiInv f} : IsEquiv f.
Proof.
  snapply isequiv_adjointify.
  - apply (sect_biinv f).
  - apply eisretr_biinv.  (* We provide proof of eissect, but it gets modified. *)
  - intro a.
    lhs napply sect_retr_homotopic_isbiinv.
    apply eissect_biinv.
Defined.

Global Instance isequiv_isbiinv_sect {A B : Type} (f : A -> B) `{bi : !IsBiInv f} : IsEquiv (sect_biinv f)
  := isequiv_inverse f (feq := (isequiv_isbiinv' f)).

Definition isbiinv_isequiv `(f : A -> B)
  : IsEquiv f -> IsBiInv f.
Proof.
  intros [g s r adj].
  exact (Build_IsBiInv _ _ f g g s r).
Defined.

Definition iff_isbiinv_isequiv `(f : A -> B)
  : IsBiInv f <-> IsEquiv f.
Proof.
  split.
  - apply isequiv_isbiinv.
  - apply isbiinv_isequiv.
Defined.

(** This uses implicitly that the product of contractible types is contractible. *)
Global Instance ishprop_isbiinv `{Funext} `(f : A -> B) : IsHProp (IsBiInv f) | 0.
Proof.
  apply hprop_inhabited_contr.
  intros bif.
  srapply (contr_equiv' _ (prod_isbiinv A B)).
Defined.

Definition equiv_isbiinv_isequiv `{Funext} `(f : A -> B)
  : IsBiInv f <~> IsEquiv f.
Proof.
  apply equiv_iff_hprop_uncurried, iff_isbiinv_isequiv.
Defined.

(** Some lemmas to send equivalences and biinvertible maps back and forth. *)

Definition equiv_biinv A B (f : BiInv A B) : A <~> B
  := Build_Equiv A B f _.

Definition biinv_equiv A B (e : A <~> B) : BiInv A B
  := Build_BiInv A B e (isbiinv_isequiv e (equiv_isequiv e)).

Definition equiv_biinv_equiv `{Funext} A B
  : BiInv A B <~> (A <~> B) .
Proof.
  refine ((issig_equiv A B) oE _ oE (issig_BiInv A B)^-1).
  rapply (equiv_functor_sigma_id equiv_isbiinv_isequiv).
Defined.

Definition idmap_biinv (A : Type) : BiInv A A.
Proof.
  by nrefine (Build_BiInv A A idmap (Build_IsBiInv A A idmap idmap idmap _ _ )).
Defined.

(** Assume we have a commutative square [e' o f == g o e] in which [e] and [e'] are bi-invertible. Then [f] and [g] also commute with the retractions and sections, and the homotopies in these new squares each satisfy a coherence condition. *)

Section EquivalenceCompatibility.

  Context {A B C D : Type}.
  Context (e : BiInv A B) (e' : BiInv C D) (f : A -> C) (g : B -> D).

  Let s := sect_biinv e.
  Let r := retr_biinv e.
  Let re := eissect_biinv e : r o e == idmap.
  Let es := eisretr_biinv e: e o s == idmap.
  Let s' := sect_biinv e'.
  Let r' := retr_biinv e'.
  Let re' := eissect_biinv e' : r' o e' == idmap.
  Let es' := eisretr_biinv e' : e' o s' == idmap.

  Definition helper_r (pe : e' o f == g o e) : r' o g o e == f o r o e.
  Proof.
    intro x.
    exact ((ap r' (pe x))^ @ (re' (f x) @ (ap f (re x))^)).
  Defined.

  Definition helper_s (pe : e' o f == g o e) : e' o s' o g == e' o f o s.
  Proof.
    intro y.
    exact (es' (g y) @ (ap g (es y))^ @ (pe (s y))^).
  Defined.

  (** The following lemmas express each one of these coherence conditions mentioned above.*)

  Definition biinv_compat_pr (pe : forall (x : A), e' (f x) = g (e x))
    : forall (y : B), r' (g y) = f (r y).
  Proof.
    - apply (equiv_ind e).
      apply (helper_r pe).
  Defined.

  Definition biinv_compat_ps (pe : forall (x : A), e' (f x) = g (e x))
    : forall (y : B), s' (g y) = f (s y).
  Proof.
    intro y.
    apply (equiv_inj e'); cbn.
    apply (helper_s pe).
  Defined.

  Definition biinv_compat_pre (pe : forall (x : A), e' (f x) = g (e x))
    : forall (x : A), re' (f x) = ap r' (pe x) @ (biinv_compat_pr pe) (e x) @ ap f (re x).
  Proof.
    intro x.
    unfold biinv_compat_pr.
    rewrite equiv_ind_comp.
    apply moveL_pM.
    apply moveL_Mp.
    reflexivity.
  Defined.

  Definition biinv_compat_pes (pe : forall (x : A), e' (f x) = g (e x))
    : forall (y : B), es' (g y) = ap e' ((biinv_compat_ps pe) y) @ pe (s y) @ ap g (es y).
  Proof.
    intro y; cbn beta.
    rewrite equiv_inj_comp.
    apply moveL_pM.
    apply moveL_pM.
    reflexivity.
  Defined.

End EquivalenceCompatibility.
