(* Copyright 2025 Ross Tate
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(* Rocq Formalization and Verification for the OOPSLA 2025 Article 'Type-Outference with Label-Listeners: Foundations for Decidable Type-Consistency for Nominal Object-Oriented Generics'
 * Version 1.0
 * by Ross Tate
 * 2025
 * doi:10.1145/3747411 (The OOPSLA 2025 article can be found at doi:10.1145/3763797)
 * Requires Rocq 8.17
 *)

(* The mechanization is comprised of the following parts:
 * Part 1: Preliminaries - components of the mechanization that are not specific to the paper
 * Part 2: Programs - definition of programs in the calculus
 * Part 3: Type-Consistency - definition of type spaces, type-space consistency, and type-consistency
 * Part 4: Safety - proof that type-consistency ensures progress and preservation
 * Part 5: Graphical Cores - definition of graphical cores, histories (which generalize configurations), and constraint-derivation
 * Part 6: Models - definition of modeling and of a graphical core's type space
 * Part 7: Graphical-Core Consistency - definition of consistency of a graphical core with a particular history
 * Part 8: Correspondence - proof of correspondence between type-space consistency and graphical-core consistency
 * Part 9: Configurations - finitary specializations of graphical cores and histories
 * Part 10: Algorithm - proof that graphical-core consistency is decidable
 * Part 11: Extraction - process for extracting a graphical core from a program
 * Part 12: Decidability - proof that type-consistency is decidable
 *)

(* The analogs of the following figures, definitions, lemmas, and theorems of the paper can be found at the indicated locations within this mechanization:
 * Figure 6: Grammar - Part 2
 * Figure 7: Operational Semantics - Part 2.3
 * Figure 8: Type Validity - Part 2.6
 * Lemma 6.1: Decidability of Type Validity - Part 12.1
 * Figure 9: Hierarchy Validity - Part 2.6
 * Lemma 6.2: Decidability of Hierarchy Validity - Part 12.2
 * Definition 7.1: Type Space - Part 3.1
 * Figure 10: User Subtyping - Part 3.5
 * Theorem 7.2: Consistency of the User Type Space - Part 3.5
 * Figure 11: Type-Checking - Part 3.2 and Part 3.3
 * Figure 12: Type-Space Consistency - Part 3.4
 * Theorem 7.3: Safety of Type-Space Consistency - Part 4
 * Figure 13: Type-Consistency - Part 3.6
 * Definition 8.1: Graphical Core - Part 5.1
 * Definition 8.2: Configuration - Part 5.3 and Part 9
 * Figure 14: Derived Constraints - Part 5.4 and Part 5.6
 * Lemma 8.3: Computability of Derived Constraints - Part 10.2
 * Figure 15: Graphical-Core Consistency - Part 7
 * Theorem 8.4: Decidiablity of Graphical-Core Consistency - Part 10.3
 * Figure 16: Modeling Graphical Cores with Type Spaces - Part 6.1
 * Lemma 9.1: Extractability of Graphical Cores from Expressions - Part 11
 * Figure 17: Type-Checkability - Part 11.4
 * Lemma 9.2: Type-Checking implies Type-Checkability - Part 11.4
 * Lemma 9.3: Decidability of Type-Checkability - Part 12.3
 * Figure 18: The Canonical Type Space of a Graphical Core - Part 6.2
 * Lemma 9.4: A Graphical Core is Modeled by its Canonical Type Space - Part 6.3
 * Lemma 9.5: Consistency of a Graphical Core implies Consistency of its Canonical Type Space - Part 8.2
 * Lemma 9.6: Consistency of a Model of a Graphical Core implies Consistency of the Graphical Core - Part 8.4
 * Theorem 9.7: Decidability of Type-Consistent Program Validity - Part 12.4
 *)

(* The expectation is that, after reading the paper for the high-level insights, one reads the comments as one steps through the document.
 * The reader is expected to jump over the individual proofs rather than step through them tactic by tactic.
 * That said, we use little automation and try to be diligent with naming intermediate variables, so one can reasonably step through a proof to get a detailed understanding of how it works if one wants.
 *)

(* Part 1: Preliminaries
 * Here we provide the components of the mechanization that are not specific to the paper.
 *)

Set Uniform Inductive Parameters.
Set Primitive Projections.
Set Printing Projections.



(* Part 1.1: Strict Propositions
 * We make heavy use of strict propositions.
 * All terms of a strict proposition or considered to be definitionally equal.
 * This makes the use of strict propositions in definitions much more convenient.
 *)

Inductive Squash {P: Prop}: SProp
:= squash: P -> Squash.
Arguments Squash : clear implicits.

Inductive Box {P: SProp}: Prop
:= box: P -> Box.
Arguments Box : clear implicits.

Inductive exSP {P: SProp} {P': P -> Prop}: Prop
:= ex_introSP (p: P) (p': P' p).
Arguments exSP [_] _.
Notation "'existsSP' x .. y , p" := (exSP (fun x => .. (exSP (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsSP' '/ ' x .. y , '/ ' p ']'")
  : type_scope.
Inductive exTS {T: Type} {P: T -> SProp}: SProp
:= ex_introTS (t: T) (p: P t).
Arguments exTS [_] _.
Notation "'existsTS' x .. y , p" := (exTS (fun x => .. (exTS (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsTS' '/ ' x .. y , '/ ' p ']'")
  : type_scope.
Record exSS {P: SProp} {P': P -> SProp}: SProp := ex_introSS
{ proj1_exSS: P;
  proj2_exSS: P' proj1_exSS;
}.
Arguments exSS [_] _.
Notation "'existsSS' x .. y , p" := (exSS (fun x => .. (exSS (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsSS' '/ ' x .. y , '/ ' p ']'")
  : type_scope.
Inductive exTSS {T: Type} {P1: T -> SProp} {P2: T -> SProp}: SProp
:= ex_introSSS (t: T) (p1: P1 t) (p2: P2 t).
Arguments exTSS [_] _ _.
Notation "'existsTSS' x , p & q" := (exTSS (fun x => p) (fun x => q))
  (at level 200, x name, p at level 200, right associativity) : type_scope.
Notation "'existsTSS' x : A , p & q" := (@exTSS A (fun x => p) (fun x => q))
  (at level 200, x name, A at level 200, p at level 200, right associativity,
    format "'[' 'existsTSS' '/ ' x : A , '/ ' '[' p & '/' q ']' ']'")
  : type_scope.
Inductive exTSP {T: Type} {P1: T -> SProp} {P2: T -> Prop}: Prop
:= ex_introTSP (t: T) (p1: P1 t) (p2: P2 t).
Arguments exTSP [_] _ _.
Notation "'existsTSP' x , p & q" := (exTSP (fun x => p) (fun x => q))
  (at level 200, x name, p at level 200, right associativity) : type_scope.
Notation "'existsTSP' x : A , p & q" := (@exTSP A (fun x => p) (fun x => q))
  (at level 200, x name, A at level 200, p at level 200, right associativity,
    format "'[' 'existsTSP' '/ ' x : A , '/ ' '[' p & '/' q ']' ']'")
  : type_scope.

Record sigS {T: Type} {P: T -> SProp}: Type := existS
{ proj1_sigS: T;
  proj2_sigS: P proj1_sigS;
}.
Arguments sigS [_] _.

Record sigSdT {A: Type} {P: A -> SProp} {B: forall a: A, P a -> Type}: Type := existSdT
{ proj1_sigSdT: A;
  proj2_sigSdT: P proj1_sigSdT;
  proj3_sigSdT: B proj1_sigSdT proj2_sigSdT;
}.
Arguments sigSdT [_] _ _.
Arguments existSdT {_ _ _} _ _ _.

Inductive FalseS: SProp
:=.
Definition falseSe {T: Type} (f: FalseS): T
:= match f with end.
Definition false_falseS (f: False): FalseS
:= match f with end.
Definition falseS_false: FalseS -> False
:= falseSe.

Inductive TrueS: SProp
:= trueS.

Record AndS {F S: SProp}: SProp := conjS
{ proj1_AndS: F;
  proj2_AndS: S;
}.
Arguments AndS : clear implicits.

Inductive OrS {L R: SProp}: SProp
:= oleftS (l: L)
 | orightS (r: R).
Arguments OrS : clear implicits.

Inductive eqS {T: Type} (t: T): T -> SProp
:= eqS_refl: eqS t.
Arguments eqS [_] _ _.

Lemma eq_eqS {T: Type} {t t': T}: t = t' -> eqS t t'.
Proof.
  intro e.
  destruct e.
  reflexivity.
Qed.
Lemma eqS_squash_eq {T: Type} {t t': T} (e: eqS t t'): Squash (t = t').
Proof.
  destruct e.
  constructor.
  reflexivity.
Qed.
Lemma eqS_sym {T: Type} {t t': T} (e: eqS t t'): eqS t' t.
Proof.
  destruct e.
  reflexivity.
Qed.
Lemma eqS_trans {T: Type} {t t' t'': T} (e: eqS t t') (e': eqS t' t''): eqS t t''.
Proof.
  destruct e'.
  assumption.
Qed.

Inductive eqSProp {P: SProp} (p: P): P -> Prop
:= eqSProp_refl: eqSProp p.
Definition eqSProp_total {P: SProp} (p p': P): eqSProp p p' := eqSProp_refl p.
Ltac merge p p' := destruct (eqSProp_total p p').
Ltac merge_refl e := destruct (eqSProp_total (eqS_refl _) e).



(* Part 1.2: Basic Types and Operations *)

Definition compose {T T' T'': Type} (f: T -> T') (f': T' -> T'') (t: T): T''
:= f' (f t).



Definition Unit: Type := unit.



Inductive empty: Prop
:=.
Definition Empty: Type
:= empty.
Definition emptye {T: Type} (empty: Empty): T
:= match empty with end.
Definition emptyde {T: Empty -> Type} (empty: Empty): T empty
:= match empty with end.
Definition emptydSe {T: Empty -> SProp} (empty: Empty): T empty
:= match empty with end.



Definition optione {A: Type} {K: Type} (kn: K) (ks: A -> K) (o: option A): K
:= match o with
   | None => kn
   | Some a => ks a
   end.
Lemma Some_inj {T: Type} {t t': T}: Some t = Some t' -> t = t'.
Proof.
  intro e.
  injection e.
  trivial.
Qed.
Definition OptionS {A: Type} (P: A -> SProp): option A -> SProp
:= optione TrueS P.



Definition sume {L R: Type} {K: Type} (kl: L -> K) (kr: R -> K) (s: sum L R): K
:= match s with
   | inl l => kl l
   | inr r => kr r
   end.
Definition sum_mapr {L R R': Type} (rmap: R -> R') (s: sum L R): sum L R'
:= match s with
   | inl l => inl l
   | inr r => inr (rmap r)
   end.
Lemma inl_inj {L R: Type} {l l': L}: @inl L R l = inl l' -> l = l'.
Proof.
  intro e.
  injection e.
  trivial.
Qed.
Lemma inr_inj {L R: Type} {r r': R}: @inr L R r = inr r' -> r = r'.
Proof.
  intro e.
  injection e.
  trivial.
Qed.



Require Import List.

Inductive ListContains {T: Type} {t: T}: list T -> SProp
:= lchead (tail: list T): ListContains (cons t tail)
 | lctail (head: T) (tail: list T): ListContains tail -> ListContains (cons head tail).
Arguments ListContains {_} _ _.

Lemma contains_map {T T': Type} (f: T -> T') (t: T) (l: list T): ListContains t l -> ListContains (f t) (map f l).
Proof.
  intro contains.
  induction l.
  + inversion contains.
  + inversion contains; subst.
    - apply lchead.
    - apply lctail.
      apply IHl.
      assumption.
Qed.
Lemma map_contains {T T': Type} (f: T -> T') (t': T') (l: list T): ListContains t' (map f l) -> existsTSS t: T, eqS (f t) t' & ListContains t l.
Proof.
  intro contains.
  induction l; simpl in contains.
  + inversion contains.
  + inversion contains; clear contains; subst.
    - eexists; try reflexivity.
      apply lchead.
    - destruct IHl as [ t e contains ]; try assumption.
      exists t; try assumption.
      apply lctail.
      assumption.
Qed.

Lemma contains_app_l {T: Type} (t: T) (l l': list T): ListContains t l -> ListContains t (app l l').
Proof.
  intro contains.
  induction l as [ | t' l IHl ]; simpl.
  + inversion contains.
  + inversion contains; subst.
    - apply lchead.
    - apply lctail.
      auto.
Qed.
Lemma contains_app_r {T: Type} (t: T) (l l': list T): ListContains t l' -> ListContains t (app l l').
Proof.
  intro contains.
  induction l as [ | t' l IHl ]; simpl.
  + assumption.
  + apply lctail.
    assumption.
Qed.
Lemma app_contains {T: Type} (t: T) (l l': list T): ListContains t (app l l') -> OrS (ListContains t l) (ListContains t l').
Proof.
  intro contains.
  induction l as [ | t' l IHl ]; simpl in *.
  + right.
    assumption.
  + inversion contains; subst.
    - left.
      apply lchead.
    - destruct IHl as [ IHl | IHl ]; try assumption.
      * left.
        apply lctail.
        assumption.
      * right.
        assumption.
Qed.

Definition ListForallS {T: Type} (P: T -> SProp): list T -> SProp
:= fix ListForallS (l: list T): SProp
:= match l with
   | nil => TrueS
   | cons t l => AndS (P t) (ListForallS l)
   end.

Lemma forall_listforallS {T: Type} {P: T -> SProp} {l: list T}: (forall t: T, ListContains t l -> P t) -> ListForallS P l.
Proof.
  intro containsp.
  induction l as [ | t l IHl ]; simpl.
  + split.
  + split.
    - apply containsp.
      apply lchead.
    - apply IHl.
      intros t' contains'.
      apply containsp.
      apply lctail.
      assumption.
Qed.
Lemma listforallS_forall {T: Type} {P: T -> SProp} {l: list T}: ListForallS P l -> (forall t: T, ListContains t l -> P t).
Proof.
  induction l as [ | t l IHl ]; simpl.
  + intros _ t contains.
    inversion contains.
  + intros [ p fa ].
    intros t' contains'.
    inversion contains'; auto.
Qed.

Lemma listforallS_mono {T: Type} (P P': T -> SProp) (l: list T): (forall t: T, P t -> P' t) -> ListForallS P l -> ListForallS P' l.
Proof.
  intros pp' fa.
  apply forall_listforallS.
  intros t contains.
  apply pp'.
  eapply listforallS_forall; eassumption.
Qed.

Lemma forall_app {T: Type} (P: T -> SProp) (l l': list T): ListForallS P l -> ListForallS P l' -> ListForallS P (app l l').
Proof.
  intros fa fa'.
  apply forall_listforallS.
  intros t contains.
  apply app_contains in contains.
  destruct contains as [ contains | contains ]; revert t contains; apply listforallS_forall; assumption.
Qed.

Lemma forall_map {T T': Type} (f: T -> T') (P: T' -> SProp) (l: list T): ListForallS (fun t => P (f t)) l -> ListForallS P (map f l).
Proof.
  induction l; simpl.
  + trivial.
  + intros [ p fa ].
    split; auto.
Qed.

Definition PairListContains {A B: Type} (l: list (prod A B)) (a: A) (b: B): SProp
:= ListContains (pair a b) l.



Inductive SumBoolS {P P': SProp}: Type
:= sbleftS (p: P)
 | sbrightS (p': P').
Arguments SumBoolS : clear implicits.
Definition DeciderS (P: SProp): Type
:= SumBoolS P (P -> FalseS).



(* Part 1.3: Variance *)

Inductive Sign: Type
:= negative | positive.

Definition negate (sign: Sign): Sign
:= match sign with
   | negative => positive
   | positive => negative
   end.
Definition multiply (sign: Sign): Sign -> Sign
:= match sign with
   | negative => negate
   | positive => fun sign => sign
   end.



(* Due to variance, we often need to flip the order of the arguments depending on the variance at hand. *)
Definition Signed {A: Type} (R: A -> A -> SProp) (sign: Sign): A -> A -> SProp
:= match sign with
   | negative => fun a a' => R a' a
   | positive => R
   end.

Lemma signed_negate' {A: Type} (R: A -> A -> SProp) (sign: Sign) (a a': A): Signed R (negate sign) a a' -> Signed R sign a' a.
Proof.
  destruct sign; trivial.
Qed.

Lemma signed_mono {A: Type} (R R': A -> A -> SProp) (mono: forall a a': A, R a a' -> R' a a') (sign: Sign) (a a': A): Signed R sign a a' -> Signed R' sign a a'.
Proof.
  destruct sign; apply mono.
Qed.
Lemma signed_refl {A: Type} (R: A -> A -> SProp) (sign: Sign) (a: A): R a a -> Signed R sign a a.
Proof.
  destruct sign; trivial.
Qed.
Lemma signed_trans {A: Type} (R: A -> A -> SProp) (trans: forall a a' a'': A, R a a' -> R a' a'' -> R a a'') (sign: Sign) (a a' a'': A): Signed R sign a a' -> Signed R sign a' a'' -> Signed R sign a a''.
Proof.
  intros.
  destruct sign; apply trans with a'; assumption.
Qed.



(* Signed has better reduction behavior, but ISigned keeps its use of R stricly positive, so it can be used in co/inductive definitions. *)
Inductive ISigned {A: Type} {R: A -> A -> SProp}: Sign -> A -> A -> SProp
:= isnegative (a a': A): R a' a -> ISigned negative a a'
 | ispositive (a a': A): R a a' -> ISigned positive a a'.
Arguments ISigned {_} _ _ _ _.

Lemma isigned_signed {A: Type} {R: A -> A -> SProp} {sign: Sign} {a a': A}: ISigned R sign a a' -> Signed R sign a a'.
Proof.
  intros signed.
  destruct signed; assumption.
Qed.
Lemma signed_isigned {A: Type} {R: A -> A -> SProp} {sign: Sign} {a a': A}: Signed R sign a a' -> ISigned R sign a a'.
Proof.
  intros signed.
  destruct sign; constructor; assumption.
Qed.



(* Part 1.4: Cardinality
 * The following are our formalizations of various standard (constructive) cardinalities.
 *)

(* Decidable strict propositions are an important class *)
Class DecidableS (P: SProp): Type
:= decidableS: DeciderS P.
Arguments decidableS _ {_}.

#[local] Instance TrueS_DecidableS: DecidableS TrueS.
Proof.
  left.
  constructor.
Qed.
#[local] Instance FalseS_DecidableS: DecidableS FalseS.
Proof.
  right.
  trivial.
Qed.



(* Our adaptation of "axiom" K *)
Definition K {T: Type} (t: T): Prop
:= forall e: t = t, eq_refl = e.

Definition projT1_eq {A: Type} {T: A -> Type} {s s': sigT T} (e : s = s'): projT1 s = projT1 s'
:= match e with eq_refl => eq_refl (projT1 s) end.
Definition projT2_eq {A: Type} {T: A -> Type} {s s': sigT T} (e : s = s'): match projT1_eq e in _ = a' return T a' with eq_refl => projT2 s end = projT2 s'
:= match e as e in _ = s' return match projT1_eq e in _ = a' return T a' with eq_refl => projT2 s end = projT2 s' with eq_refl => eq_refl (projT2 s) end.
Definition k_inj_projT2 {A: Type} {T: A -> Type} {a: A} (k: K a) [t t': T a] (e : existT T a t = existT T a t'): t = t'
:= match k (projT1_eq e) in _ = e' return match e' in _ = a' return T a' with eq_refl => t end = t' -> t = t' with eq_refl => fun e => e end (projT2_eq e).

Definition proj1_sigSdT_eq {A: Type} {P: A -> SProp} {T: forall a: A, P a -> Type} {s s': sigSdT P T} (e : s = s'): proj1_sigSdT s = proj1_sigSdT s'
:= match e with eq_refl => eq_refl s.(proj1_sigSdT) end.
Definition proj3_sigSdT_eq {A: Type} {P: A -> SProp} {T: forall a: A, P a -> Type} {s s': sigSdT P T} (e : s = s'): match proj1_sigSdT_eq e as e in _ = a' return T a' (match e with eq_refl => s.(proj2_sigSdT) end) with eq_refl => s.(proj3_sigSdT) end = s'.(proj3_sigSdT)
:= match e as e in _ = s' return match proj1_sigSdT_eq e as e in _ = a' return T a' (match e with eq_refl => s.(proj2_sigSdT) end) with eq_refl => s.(proj3_sigSdT) end = s'.(proj3_sigSdT) with eq_refl => eq_refl s.(proj3_sigSdT) end.
Definition k_inj_proj3_sigSdT {A: Type} {P: A -> SProp} {T: forall a: A, P a -> Type} {a: A} {p: P a} (k: K a) [t t': T a p] (e : existSdT a p t = existSdT a p t'): t = t'
:= match k (proj1_sigSdT_eq e) in _ = e' return match e' in _ = a' return T a' (match e' with eq_refl => p end) with eq_refl => t end = t' -> t = t' with eq_refl => fun e => e end (proj3_sigSdT_eq e).

(* An H-Set is one wherein all proofs of equality are equal.
 * In particular, (existT B a b) = (existT B a b') implies b = b' when a belongs to an H-Set.
 * We use this to define a custom inversion_hset tactic that extends inversion to incorporate such reasoning about H-Sets.
 *)
Class HSet (T: Type): Prop
:= uip (t: T): K t.
Definition hset_inj_projT2 {A: Type} `{HSet A} {T: A -> Type} {a: A}: forall [t t': T a], (existT T a t = existT T a t') -> t = t'
:= k_inj_projT2 (uip a).
Lemma eq_eq `{A: Type} `{HSet A} {a a': A} (e e': a = a'): e = e'.
  destruct e.
  apply uip.
Qed.

(* In some cases, this property can only be ensured for a subset of the type. *)
Class HSetS {T: Type} (P: T -> SProp): Prop
:= uipS (t: T) (p: P t): K t.
#[local] Hint Extern 5 (HSetS ?T (fun x => ?P x)) => change (HSetS T P) : typeclass_instances.
Definition hsetS_inj_proj3_sigSdT {A: Type} {P: A -> SProp} `{HSetS A P} {T: forall a: A, P a -> Type} {a: A} {p: P a}: forall [t t': T a p], (existSdT a p t = existSdT a p t') -> t = t'
:= k_inj_proj3_sigSdT (uipS a p).

Ltac deq_hset
:= repeat (match goal with
           | [ e: @existT _ _ ?index _ = @existT _ _ ?index _ |- _] => apply hset_inj_projT2 in e; subst
           | [ e: @existSdT _ _ _ ?index _ _ = @existSdT _ _ _ ?index _ _ |- _] => apply hsetS_inj_proj3_sigSdT in e; subst
           end).
Ltac inversion_hset h
:= inversion h;
   clear h;
   subst;
   deq_hset.



(* An S-Set is one wherein a proof of equality can be recovered from knowing two values are equal without knowing how they are equal.
 * This means we can use strict (i.e. definitionally equal) equality in place of non-strict equality; the convert function provides this funcitonality.
 * It also implies the type is also an H-Set.
 * Note that, while H-Sets are a standard notion from Homotopy Type Theory, we know of know prior notion of S-Set.
 *)
Class SSet (T: Type): Prop
:= eqS_eq [t t': T] (e: eqS t t'): eq t t'.
#[local] Instance SSet_HSet (T: Type) `{SSet T}: HSet T.
  intros t e.
  replace eq_refl with (match eqS_eq (eqS_refl t) in _ = t' return t' = t with eq_refl => eqS_eq (eqS_refl t) end).
  + replace e with (match eqS_eq (eqS_refl t) in _ = t' return t' = t with eq_refl => eqS_eq (match e in _ = t' return eqS t t' with eq_refl => eqS_refl _ end) end).
    - destruct (eqS_eq (eqS_refl _)).
      reflexivity.
    - destruct e.
      destruct (eqS_eq (eqS_refl _)).
      reflexivity.
  + destruct (eqS_eq (eqS_refl _)).
    reflexivity.
Qed.

Definition convert {A: Type} `{SSet A} {a: A} {a': A} (e: eqS a a') (B: A -> Type) (b: B a): B a'
:= match eqS_eq e with eq_refl => b end.
Lemma convert_id {A: Type} `{SSet A} {a: A} (e: eqS a a): convert e = fun B b => b.
Proof.
  unfold convert.
  rewrite (eq_eq (eqS_eq e) eq_refl).
  reflexivity.
Qed.
Opaque convert.
Lemma convert_convert {A: Type} `{SSet A} (B: A -> Type) {a a' a'': A} (b: B a) (e: eqS a a') (e': eqS a' a''): convert e' B (convert e B b) = convert (eqS_trans e e') B b.
Proof.
  revert e.
  generalize e'.
  apply (convert e').
  clear e'.
  intros e' e.
  rewrite convert_id.
  reflexivity.
Qed.
Definition convertS {A: Type} `{SSet A} {a: A} {a': A} (e: eqS a a') (P: A -> SProp) (p: P a): P a'
:= match eqS_eq e with eq_refl => p end.
Lemma convertS_id {A: Type} `{SSet A} {a: A} (e: eqS a a): eqSProp (convertS e) (fun B b => b).
Proof.
  reflexivity.
Qed.
Opaque convertS.



(* Equality is decidable for many types.
 * This is useful algorithmically, and it implies the type is an S-Set.
 *)
Class DecEq (T: Type): Type
:= dec_eq (t t': T): {t = t'} + {t = t' -> False}.

#[local] Instance DecEq_SSet (T: Type) `{DecEq T}: SSet T.
  intros t t' e.
  destruct (dec_eq t t') as [ ? | ne ]; try assumption.
  elimtype FalseS.
  destruct e.
  apply false_falseS.
  apply ne.
  reflexivity.
Qed.

#[local] Instance DecEq_DecidableS (T: Type) {T_DecEq: DecEq T} (t t': T): DecidableS (eqS t t').
Proof.
  destruct (dec_eq t t') as [ e | ne ].
  + left.
    destruct e.
    reflexivity.
  + right.
    intro e.
    destruct e.
    apply false_falseS.
    apply ne.
    reflexivity.
Qed.

Definition inj_DecEq {A: Type} {B: Type} `{deB: DecEq B} (f: A -> B) (finj: forall [a a': A], f a = f a' -> a = a'): DecEq A
:= fun a a' => match dec_eq (f a) (f a') with
               | left e => left (finj e)
               | right ne => right (fun e => ne (match e in _ = a' return f a = f a' with eq_refl => eq_refl (f a) end))
               end.



(* We use binary paths, i.e. BPaths, as our standard countable type. *)
Inductive BPath: Type
:= bend
 | bfirst (path: BPath)
 | bsecond (path: BPath).

#[local] Instance BPath_DecEq: DecEq BPath.
  intro path.
  induction path; intro path'; destruct path'; try ((left; reflexivity) || (right; intro e; inversion e; fail)).
  + destruct (IHpath path') as [ e | ne ].
    - left; f_equal; assumption.
    - right; intro e; inversion e; auto.
  + destruct (IHpath path') as [ e | ne ].
    - left; f_equal; assumption.
    - right; intro e; inversion e; auto.
Qed.

(* This function encodes a pair of paths as a single path. *)
Fixpoint bpath_pair (first: BPath): BPath -> BPath
:= match first with
   | bend => bfirst
   | bfirst first => fun second => bsecond (bfirst (bpath_pair first second))
   | bsecond first => fun second => bsecond (bsecond (bpath_pair first second))
   end.
Lemma bpath_pair_inj1 (first first': BPath) (second second': BPath): bpath_pair first second = bpath_pair first' second' -> first = first'.
  revert first' second second'; induction first; intros first' second second' e; destruct first'; simpl in e; inversion e; clear e; rename H0 into e; f_equal; eauto.
Qed.
Lemma bpath_pair_inj2 (first first': BPath) (second second': BPath): bpath_pair first second = bpath_pair first' second' -> second = second'.
  revert first' second second'; induction first; intros first' second second' e; destruct first'; simpl in e; inversion e; clear e; rename H0 into e; eauto.
Qed.
Lemma bpath_pair_inj (first first': BPath) (second second': BPath): bpath_pair first second = bpath_pair first' second' -> first = first' /\ second = second'.
  intro e.
  split; revert e.
  + apply bpath_pair_inj1.
  + apply bpath_pair_inj2.
Qed.

Fixpoint bpath_fst (path: BPath): BPath
:= match path with
   | bfirst path => bend
   | bsecond (bfirst path) => bfirst (bpath_fst path)
   | bsecond (bsecond path) => bsecond (bpath_fst path)
   | _ => bend
   end.
Fixpoint bpath_snd (path: BPath): BPath
:= match path with
   | bfirst path => path
   | bsecond (bfirst path) => bpath_snd path
   | bsecond (bsecond path) => bpath_snd path
   | _ => bend
   end.



(* A subcountable type is one with an injection into a countable set.
 * This is useful for data-structures, and it ensures equality is decidable.
 *)
Class SubCountable (T: Type) :=
{ scpath: T -> BPath;
  scpath_inj: forall [t t': T], scpath t = scpath t' -> eq t t'
}.
#[local] Instance SubCountable_DecEq (T: Type) `{SubCountable T}: DecEq T
:= inj_DecEq scpath scpath_inj.

(* In some cases, only a subset of the type is subcountable. *)
Class SubCountableS {T: Type} (P: T -> SProp) :=
{ scpathS: forall t: T, P t -> BPath;
  scpathS_inj: forall [t t': T], forall [p : P t], forall [p': P t'], scpathS t p = scpathS t' p' -> eq t t'
}.

Lemma scpath_injS {T: Type} {T_SubCountable: SubCountable T} {t t': T}: eqS (scpath t) (scpath t') -> eqS t t'.
Proof.
  intro e.
  apply eq_eqS.
  apply scpath_inj.
  apply eqS_eq.
  assumption.
Qed.

Definition inj_SubCountable {A: Type} {B: Type} {scB: SubCountable B} (f: A -> B) (finj: forall [a a': A], f a = f a' -> a = a'): SubCountable A :=
{| scpath a := scpath (f a);
   scpath_inj a a' e := finj (scpath_inj e)
|}.
Definition inj_SubCountableS {A: Type} {P: A -> SProp} {B: Type} {P': B -> SProp} {scP': SubCountableS P'} (f: forall a: A, P a -> B) (fp: forall a: A, forall p: P a, P' (f a p)) (finj: forall [a a': A], forall p: P a, forall p': P a', f a p = f a' p' -> a = a'): SubCountableS P :=
{| scpathS a p := scpathS (f a p) (fp a p);
   scpathS_inj a a' p p' e := finj p p' (scpathS_inj e)
|}.

#[local] Instance SubCountableS_HSetS {T: Type} (P: T -> SProp) {P_SubCountableS: SubCountableS P}: HSetS P.
Proof.
  intros t p.
  set (ecanon := fun (t': T) (p': P t') (e: t = t') => match decidableS (eqS (scpathS t p) (scpathS t' p')) with sbleftS e => scpathS_inj (eqS_eq e) | sbrightS ne => match ne (match e in _ = t' return forall p': P t', eqS (scpathS t p) (scpathS t' p') with eq_refl => fun _ => eqS_refl (scpathS t p) end p') in FalseS with end end).
  assert (forall t' p' e e', ecanon t' p' e = ecanon t' p' e') as ecanon_eq.
  + unfold ecanon.
    intros t' p'.
    destruct (decidableS (eqS (scpathS t p) (scpathS t' p'))) as [ e | ne ].
    - reflexivity.
    - intro e.
      exfalso.
      apply falseS_false.
      apply ne.
      destruct e.
      merge p p'.
      reflexivity.
  + intro e.
    replace eq_refl with (match ecanon t p (eq_refl t) in _ = t' return t' = t with eq_refl => ecanon t p (eq_refl t) end).
    - replace e with (match ecanon t p (eq_refl t) in _ = t' return t' = t with eq_refl => ecanon t p e end).
      * generalize (ecanon t p (eq_refl t)) at 1 3.
        intro e'.
        destruct e'.
        apply ecanon_eq.
      * generalize p at 2.
        destruct e.
        intro p'.
        merge p p'.
        destruct (ecanon t p (eq_refl t)).
        reflexivity.
    - clear e.
      destruct (ecanon t p (eq_refl t)).
      reflexivity.
Qed.



(* A projective type is one for which choice from the set holds. *)
Class Projective (T: Type): SProp
:= projective (T': Type) (R: T -> T' -> SProp): (forall t: T, existsTS t': T', R t t') -> existsTS t': T -> T', forall t: T, R t (t' t).
Lemma projective2 {T: Type} {T_Projective: Projective T} (T': Type) (R1 R2: T -> T' -> SProp): (forall t: T, existsTSS t': T', R1 t t' & R2 t t') -> existsTSS t': T -> T', forall t: T, R1 t (t' t) & forall t: T, R2 t (t' t).
Proof.
  intro total.
  destruct (projective T' (fun t t' => AndS (R1 t t') (R2 t t'))) as [ t' H' ].
  + intro t.
    specialize (total t).
    destruct total as [ t' r1 r2 ].
    exists t'; split; assumption.
  + exists t'; intro t; apply H'.
Qed.
Lemma projectiveD {T: Type} {T_SSet: SSet T} {T_Projective: Projective T} (T': T -> Type) (R: forall t: T, T' t -> SProp): (forall t: T, existsTS t': T' t, R t t') -> existsTS t': forall t: T, T' t, forall t: T, R t (t' t).
Proof.
  intro total.
  destruct (projective2 (sigT T') (fun t s => eqS (projT1 s) t) (fun t s => R (projT1 s) (projT2 s))) as [ t' e r ].
  + intro t.
    specialize (total t).
    destruct total as [ t' r ].
    exists (existT _ t t'); try assumption.
    reflexivity.
  + exists (fun t => convert (e t) T' (projT2 (t' t))).
    intro t.
    destruct (e t).
    rewrite convert_id.
    apply r.
Qed.
Lemma projectiveD2 {T: Type} {T_SSet: SSet T} {T_Projective: Projective T} (T': T -> Type) (R1 R2: forall t: T, T' t -> SProp): (forall t: T, existsTSS t': T' t, R1 t t' & R2 t t') -> existsTSS t': forall t: T, T' t, forall t: T, R1 t (t' t) & forall t: T, R2 t (t' t).
Proof.
  intro total.
  destruct (projectiveD T' (fun t t' => AndS (R1 t t') (R2 t t'))) as [ t' H' ].
  + intro t.
    specialize (total t).
    destruct total as [ t' r1 r2 ].
    exists t'; split; assumption.
  + exists t'; intro t; apply H'.
Qed.

(* Sometimes only a subset of a type is projective. *)
Class ProjectiveS {T: Type} (P: T -> SProp): SProp
:= projectiveS (T': Type) (R: T -> T' -> SProp): (forall t: T, P t -> existsTS t': T', R t t') -> existsTS t': forall t: T, P t -> T', forall t: T, forall p: P t, R t (t' t p).
Arguments projectiveS {_} _ {_}.
Lemma projectiveS2 {T: Type} (P: T -> SProp) {P_Projective: ProjectiveS P} (T': Type) (R1 R2: T -> T' -> SProp): (forall t: T, P t -> existsTSS t': T', R1 t t' & R2 t t') -> existsTSS t': forall t: T, P t -> T', forall t: T, forall p: P t, R1 t (t' t p) & forall t: T, forall p: P t, R2 t (t' t p).
Proof.
  intro total.
  destruct (projectiveS P T' (fun t t' => AndS (R1 t t') (R2 t t'))) as [ t' H' ].
  + intros t p.
    specialize (total t p).
    destruct total as [ t' r1 r2 ].
    exists t'; split; assumption.
  + exists t'; intro t; apply H'.
Qed.
Lemma projectiveSD {T: Type} {T_SSet: SSet T} (P: T -> SProp) {P_Projective: ProjectiveS P} (T': forall t: T, P t -> Type) (R: forall t: T, forall p: P t, T' t p -> SProp): (forall t: T, forall p: P t, existsTS t': T' t p, R t p t') -> existsTS t': forall t: T, forall p: P t, T' t p, forall t: T, forall p: P t, R t p (t' t p).
Proof.
  intro total.
  destruct (projectiveS2 P (sigSdT P T') (fun t s => eqS (s.(proj1_sigSdT)) t) (fun t s => R s.(proj1_sigSdT) s.(proj2_sigSdT) s.(proj3_sigSdT))) as [ t' e r ].
  + intros t p.
    specialize (total t p).
    destruct total as [ t' r ].
    exists (existSdT t p t'); try assumption.
    reflexivity.
  + exists (fun t p => (convert (e t p) (fun t => forall p: P t, T' t p) (fun _ => (t' t p).(proj3_sigSdT))) p).
    intros t p.
    generalize (r t p).
    clear r.
    generalize (e t p).
    clear e.
    generalize (t' t p).
    intros s e.
    destruct e.
    rewrite convert_id.
    trivial.
Qed.
Lemma projectiveSD2 {T: Type} {T_SSet: SSet T} (P: T -> SProp) {P_ProjectiveS: ProjectiveS P} (T': forall t: T, P t -> Type) (R1 R2: forall t: T, forall p: P t, T' t p -> SProp): (forall t: T, forall p: P t, existsTSS t': T' t p, R1 t p t' & R2 t p t') -> existsTSS t': forall t: T, forall p: P t, T' t p, forall t: T, forall p: P t, R1 t p (t' t p) & forall t: T, forall p: P t, R2 t p (t' t p).
Proof.
  intro total.
  destruct (projectiveSD P T' (fun t p t' => AndS (R1 t p t') (R2 t p t'))) as [ t' H' ].
  + intros t p.
    specialize (total t p).
    destruct total as [ t' r1 r2 ].
    exists t'; split; assumption.
  + exists t'; intro t; apply H'.
Qed.



(* We use binary "trunks", i.e. bare binary trees, as our standard representions of finite cardinalities. *)
Inductive Optional: Type
:= oabsent
 | opresent.
Definition PresentS (o: Optional): SProp
:= match o with oabsent => FalseS | opresent => TrueS end.

Inductive BTrunk: Type
:= bleaf
 | bbranch (head: Optional) (first second: BTrunk).
Fixpoint BTContains (trunk: BTrunk): BPath -> SProp
:= match trunk with
   | bleaf => fun _ => FalseS
   | bbranch head first second => fun path => match path with
                                              | bend => PresentS head
                                              | bfirst path => BTContains first path
                                              | bsecond path => BTContains second path
                                              end
   end.

(* Although it is known that the type of binary paths is not projective in Rocq (see work on the Axiom of Countable Choice for more information),
 * the subset of paths contained within a given trunk is finite and therefore projective.
 *)
#[local] Instance BTContains_ProjectiveS (trunk: BTrunk): ProjectiveS (BTContains trunk).
Proof.
  induction trunk; simpl.
  + intros T' R total.
    exists (fun path contains => match contains in FalseS with end).
    intros ? [ ].
  + intros T' R total.
    specialize (IHtrunk1 T' (fun path => R (bfirst path)) (fun path => total (bfirst path))).
    destruct IHtrunk1 as [ t'1 IHtrunk1 ].
    specialize (IHtrunk2 T' (fun path => R (bsecond path)) (fun path => total (bsecond path))).
    destruct IHtrunk2 as [ t'2 IHtrunk2 ].
    destruct head; simpl in *.
    - clear total.
      exists (fun path => match path as path return match path with bend => FalseS | bfirst path => BTContains trunk1 path | bsecond path => BTContains trunk2 path end -> T' with bend => fun contains => match contains in FalseS with end | bfirst path => t'1 path | bsecond path => t'2 path end).
      intros [ | path | path ]; try auto.
      intros [ ].
    - specialize (total bend trueS).
      destruct total as [ t' r ].
      exists (fun path => match path as path return match path with bend => TrueS | bfirst path => BTContains trunk1 path | bsecond path => BTContains trunk2 path end -> T' with bend => fun _ => t' | bfirst path => t'1 path | bsecond path => t'2 path end).
      intros [ | path | path ]; auto.
Qed.
(* This encodes a dependent pair of trunks (where the second trunk is only defined for paths contained in the first trunk) as a single trunk. *)
Fixpoint btrunk_pair (first: BTrunk): (forall path: BPath, BTContains first path -> BTrunk) -> BTrunk
:= match first as first return (forall path: BPath, BTContains first path -> BTrunk) -> BTrunk with
   | bleaf => fun _ => bleaf
   | bbranch head first second => fun second' => bbranch oabsent
                                                         (match head as head return (PresentS head -> BTrunk) -> BTrunk with
                                                         | oabsent => fun _ => bleaf
                                                         | opresent => fun second => second trueS
                                                         end (second' bend))
                                                         (bbranch oabsent
                                                                  (btrunk_pair first (fun path => second' (bfirst path)))
                                                                  (btrunk_pair second (fun path => second' (bsecond path))))
   end.
Lemma btcontains_pair (trunkf: BTrunk) (trunks: forall path: BPath, BTContains trunkf path -> BTrunk) (pathf paths: BPath): forall containsf: BTContains trunkf pathf, BTContains (trunks pathf containsf) paths -> BTContains (btrunk_pair trunkf trunks) (bpath_pair pathf paths).
Proof.
  revert trunks pathf paths; induction trunkf as [ | trunkfh trunkff IHtrunkff trunkfs IHtrunkfs ]; simpl; intros trunks pathf paths containsf containss.
  + destruct containsf.
  + destruct pathf as [ | pathf | pathf ]; simpl.
    - destruct trunkfh; destruct containsf.
      assumption.
    - eapply IHtrunkff.
      eassumption.
    - eapply IHtrunkfs.
      eassumption.
Qed.
Lemma btcontains_fst {trunkf: BTrunk} {trunks: forall path: BPath, BTContains trunkf path -> BTrunk} {path: BPath}: BTContains (btrunk_pair trunkf trunks) path -> BTContains trunkf (bpath_fst path).
Proof.
  revert path.
  induction trunkf as [ | trunkh trunkff IHtrunkff trunkfs IHtrunkfs ]; simpl; intros path contains.
  + destruct contains.
  + destruct path; simpl in *.
    - destruct contains.
    - destruct trunkh; simpl in *.
      * destruct contains.
      * constructor.
    - destruct path; simpl in *.
      * destruct contains.
      * eapply IHtrunkff.
        eassumption.
      * eapply IHtrunkfs.
        eassumption.
Qed.
Lemma btcontains_snd {trunkf: BTrunk} {trunks: forall path: BPath, BTContains trunkf path -> BTrunk} {path: BPath}: forall contains: BTContains (btrunk_pair trunkf trunks) path, BTContains (trunks (bpath_fst path) (btcontains_fst contains)) (bpath_snd path).
Proof.
  revert path.
  induction trunkf as [ | trunkh trunkff IHtrunkff trunkfs IHtrunkfs ]; simpl; intros path contains.
  + destruct contains.
  + destruct path; simpl in *.
    - destruct contains.
    - destruct trunkh; simpl in *.
      * destruct contains.
      * assumption.
    - destruct path; simpl in *.
      * destruct contains.
      * exact (IHtrunkff (fun path => trunks (bfirst path)) path contains).
      * exact (IHtrunkfs (fun path => trunks (bsecond path)) path contains).
Qed.
Lemma bpath_pair_fst_snd (trunkf: BTrunk) (trunks: forall path: BPath, BTContains trunkf path -> BTrunk) (path: BPath): BTContains (btrunk_pair trunkf trunks) path -> path = bpath_pair (bpath_fst path) (bpath_snd path).
Proof.
  revert path.
  induction trunkf as [ | trunkh trunkff IHtrunkff trunkfs IHtrunkfs ]; simpl; intros path contains.
  + destruct contains.
  + destruct path; simpl in *.
    - destruct contains.
    - destruct trunkh; simpl in *.
      * destruct contains.
      * reflexivity.
    - destruct path; simpl in *.
      * destruct contains.
      * f_equal.
        f_equal.
        eapply IHtrunkff.
        eassumption.
      * f_equal.
        f_equal.
        eapply IHtrunkfs.
        eassumption.
Qed.



(* A subfinite set is one with an injection into a finite set.
 * sftrunk specifies the trunk representing that finite set.
 * Algorithmically, this property, more so than true finiteness, is generally sufficient for ensuring termination.
 *)
Class SubFinite (T: Type): Type :=
{ SubFinite_SubCountable :: SubCountable T;
  sftrunk: BTrunk;
  sfcontains: forall t: T, BTContains sftrunk (scpath t)
}.
Arguments sftrunk _ {_}.

(* Sometimes only a subset is subfinite. *)
Class SubFiniteS {T: Type} (P: T -> SProp): Type :=
{ SubFiniteS_SubCountableS :: SubCountableS P;
  sftrunkS: BTrunk;
  sfcontainsS: forall t: T, forall p: P t, BTContains sftrunkS (scpathS t p)
}.
Arguments sftrunkS {_} _ {_}.

Definition inj_SubFinite {A: Type} {B: Type} {sfB: SubFinite B} (f: A -> B) (finj: forall [a a': A], f a = f a' -> a = a'): SubFinite A :=
{| sftrunk := sftrunk B;
   sfcontains a := (sfcontains (f a)): BTContains (sftrunk B) ((inj_SubCountable f finj).(scpath) a)
|}.
Definition inj_SubFiniteS {A: Type} {P: A -> SProp} {B: Type} {P': B -> SProp} {sfP': SubFiniteS P'} (f: forall a: A, P a -> B) {fp: forall a: A, forall p: P a, P' (f a p)} {finj: forall [a a': A], forall p: P a, forall p': P a', f a p = f a' p' -> a = a'}: SubFiniteS P :=
{| sftrunkS := sftrunkS P';
   sfcontainsS a p := (sfcontainsS (f a p) (fp a p)): BTContains (sftrunkS P') ((inj_SubCountableS f fp finj).(scpathS) a p)
|}.



(* A finite set extends the above injection to a bijection.
 * All finite sets are projective.
 * Algorithmically, finiteness is important for enumerating all values within a type.
 *)
Class Finite (T: Type): Type :=
{ Finite_SubFinite :: SubFinite T;
  fpath (path: BPath) (contains: BTContains (sftrunk T) path): T;
  fpath_eqS (path: BPath) (contains: BTContains (sftrunk T) path): eqS path (scpath (fpath path contains))
}.
Arguments fpath _ {_} _ _.

(* Sometimes only a subset is finite. *)
Class FiniteS {T: Type} (P: T -> SProp): Type :=
{ FiniteS_SubFiniteS :: SubFiniteS P;
  fpathS (path: BPath) (contains: BTContains (sftrunkS P) path): T;
  fpathSP (path: BPath) (contains: BTContains (sftrunkS P) path): P (fpathS path contains);
  fpathS_eqS (path: BPath) (contains: BTContains (sftrunkS P) path): eqS path (scpathS (fpathS path contains) (fpathSP path contains));
}.
Arguments fpathS {_} _ {_} _ _.
Arguments fpathSP {_} _ {_} _ _.

Lemma fpath_eq {T: Type} {T_Finite: Finite T} (path: BPath) (contains: BTContains (sftrunk T) path): path = scpath (fpath T path contains).
Proof.
  apply eqS_eq.
  apply fpath_eqS.
Qed.
Lemma fpath_scpath_eq {T: Type} {T_Finite: Finite T} (t: T): t = fpath T (scpath t) (sfcontains t).
Proof.
  apply scpath_inj.
  rewrite <- fpath_eq.
  reflexivity.
Qed.
Lemma fpathS_eq {T: Type} {P: T -> SProp} {P_Finite: FiniteS P} (path: BPath) (contains: BTContains (sftrunkS P) path) (p: P (fpathS P path contains)): path = scpathS (fpathS P path contains) p.
Proof.
  apply eqS_eq.
  apply fpathS_eqS.
Qed.
Lemma fpathS_scpathS_eq {T: Type} {P: T -> SProp} {P_Finite: FiniteS P} (t: T) (p: P t): t = fpathS P (scpathS t p) (sfcontainsS t p).
Proof.
  apply scpathS_inj with p (fpathSP P (scpathS t p) (sfcontainsS t p)).
  rewrite <- fpathS_eq.
  reflexivity.
Qed.

#[local] Instance Finite_Projective (T: Type) {T_Finite: Finite T}: Projective T.
Proof.
  intros T' R total.
  destruct (projectiveSD (BTContains (sftrunk T)) (fun _ _ => T') (fun path contains => R (fpath T path contains))) as [ t' r ]; try auto.
  exists (fun t => t' (scpath t) (sfcontains t)).
  intro t.
  specialize (r (scpath t) (sfcontains t)).
  rewrite <- fpath_scpath_eq in r.
  assumption.
Qed.
#[local] Instance FiniteS_ProjectiveS (T: Type) (P: T -> SProp) {P_Finite: FiniteS P}: ProjectiveS P.
Proof.
  intros T' R total.
  destruct (projectiveSD (BTContains (sftrunkS P)) (fun _ _ => T') (fun path contains => R (fpathS P path contains))) as [ t' r ]; try auto.
  + intros path contains.
    specialize (total (fpathS P path contains) (fpathSP P path contains)).
    assumption.
  + exists (fun t p => t' (scpathS t p) (sfcontainsS t p)).
    intros t p.
    specialize (r (scpathS t p) (sfcontainsS t p)).
    rewrite <- fpathS_scpathS_eq in r.
    assumption.
Qed.

Lemma bij_Finite {A: Type} {B: Type} {fB: Finite B} (f: A -> B) (g: B -> A) (finj: forall [a a': A], f a = f a' -> a = a') (fginv: forall b: B, eqS (f (g b)) b): Finite A.
Proof.
simple refine {| Finite_SubFinite := inj_SubFinite f _; fpath path (contains: BTContains (inj_SubFinite f _).(sftrunk A) path) := g (fpath B path contains) |}; try assumption.
  intros path contains.
  simpl.
  specialize (fginv (fpath B path contains)).
  apply eqS_squash_eq in fginv.
  destruct fginv as [ fginv ].
  rewrite fginv.
  apply fpath_eqS.
Qed.
Lemma bij_FiniteS {A: Type} {P: A -> SProp} {B: Type} {P' : B -> SProp} {fP: FiniteS P'} (f: forall a: A, P a -> B) (g: forall b: B, P' b -> A) (fp: forall a: A, forall p: P a, P' (f a p)) (gp: forall b: B, forall p': P' b, P (g b p')) (finj: forall [a a': A], forall p: P a, forall p': P a', f a p = f a' p' -> a = a') (fginv: forall b: B, forall p': P' b, eqS (f (g b p') (gp b p')) b): FiniteS P.
Proof.
simple refine {| FiniteS_SubFiniteS := inj_SubFiniteS f; fpathS path (contains: BTContains (inj_SubFiniteS f).(sftrunkS P) path) := g (fpathS P' path contains) (fpathSP P' path contains) |}; try assumption.
+ intros path contains.
  simpl.
  apply gp.
+ intros path contains.
  simpl.
  specialize (fginv (fpathS P' path contains) (fpathSP P' path contains)).
  apply eqS_squash_eq in fginv.
  destruct fginv as [ fginv ].
  generalize (fp (g (fpathS P' path contains) (fpathSP P' path contains)) (gp (fpathS P' path contains) (fpathSP P' path contains))).
  rewrite fginv.
  intro.
  apply eq_eqS.
  apply fpathS_eq.
Qed.

Definition btappend {T: Type}: forall trunk: BTrunk, (forall path: BPath, BTContains trunk path -> list T) -> list T
:= fix btappend (trunk: BTrunk): (forall path: BPath, BTContains trunk path -> list T) -> list T
:= match trunk with
   | bleaf => fun _ => nil
   | bbranch head first second => fun f => app (match head as head return (PresentS head -> list T) -> list T with
                                                | oabsent => fun _ => nil
                                                | opresent => fun head => head trueS
                                                end (f bend))
                                          (app (btappend first (fun path => f (bfirst path)))
                                               (btappend second (fun path => f (bsecond path))))
   end.
Definition fappend {A: Type} `{Finite A} `{B: Type} (f: A -> list B): list B
:= btappend (sftrunk A) (fun path contains => f (fpath A path contains)).
(* flist returns a list containing (f a) for all a in A. *)
Definition flist {A: Type} `{Finite A} `{B: Type} (f: A -> B): list B
:= fappend (fun a => cons (f a) nil).

Lemma contains_btappend {T: Type} (trunk: BTrunk) (f: forall path: BPath, BTContains trunk path -> list T) (path: BPath) (contains: BTContains trunk path) (t: T): ListContains t (f path contains) -> ListContains t (btappend trunk f).
Proof.
  revert f path contains; induction trunk; simpl in *; intros f path contains contains'.
  + destruct contains.
  + destruct path.
    - destruct head; destruct contains.
      apply contains_app_l.
      assumption.
    - apply contains_app_r.
      apply contains_app_l.
      apply IHtrunk1 with path contains.
      assumption.
    - apply contains_app_r.
      apply contains_app_r.
      apply IHtrunk2 with path contains.
      assumption.
Qed.
Lemma contains_fappend {A: Type} {A_Finite: Finite A} {B: Type} (f: A -> list B) (a: A) (b: B): ListContains b (f a) -> ListContains b (fappend f).
Proof.
  intro contains.
  apply contains_btappend with (scpath a) (sfcontains a).
  rewrite <- fpath_scpath_eq.
  assumption.
Qed.
Lemma contains_flist {A: Type} {A_Finite: Finite A} {B: Type} (f: A -> B) (a: A): ListContains (f a) (flist f).
Proof.
  apply contains_fappend with a.
  apply lchead.
Qed.
Lemma btappend_contains {T: Type} (trunk: BTrunk) (f: forall path: BPath, BTContains trunk path -> list T) (t: T): ListContains t (btappend trunk f) -> existsTS path: BPath, existsSS contains: BTContains trunk path, ListContains t (f path contains).
Proof.
  induction trunk; simpl in *; intro contains.
  + inversion contains.
  + apply app_contains in contains.
    destruct contains as [ contains | contains ]; [ | apply app_contains in contains; destruct contains as [ contains | contains ] ].
    - destruct head.
      * inversion contains.
      * exists bend.
        exists trueS.
        assumption.
    - apply IHtrunk1 in contains.
      destruct contains as [ path contains ].
      exists (bfirst path).
      assumption.
    - apply IHtrunk2 in contains.
      destruct contains as [ path contains ].
      exists (bsecond path).
      assumption.
Qed.
Lemma fappend_contains {A: Type} {A_Finite: Finite A} {B: Type} (f: A -> list B) (b: B): ListContains b (fappend f) -> existsTS a: A, ListContains b (f a).
Proof.
  intro contains.
  apply btappend_contains in contains.
  destruct contains as [ path [ contains contains' ] ].
  exists (fpath A path contains).
  assumption.
Qed.
Lemma flist_contains {A: Type} {A_Finite: Finite A} {B: Type} (f: A -> B) (b: B): ListContains b (flist f) -> existsTS a: A, eqS (f a) b.
Proof.
  intro contains.
  apply fappend_contains in contains.
  destruct contains as [ a contains ].
  exists a.
  inversion_hset contains.
  + reflexivity.
  + inversion H0.
Qed.

Lemma flist_forall {A: Type} {A_Finite: Finite A} {B: Type} (P: B -> SProp) (f: A -> B): (forall a: A, P (f a)) -> ListForallS P (flist f).
Proof.
  intros fa.
  apply forall_listforallS.
  intros b contains.
  apply flist_contains in contains.
  destruct contains as [ a e ].
  destruct e.
  apply fa.
Qed.

(* It is common to take a finite collection and split on whether a property holds for an element or an (opposite) property holds for all elements *)
Inductive SplitS {A: Type} {P: A -> SProp} {P': SProp}: Type
:= split_exists (a: A): P a -> SplitS
 | split_forall: P' -> SplitS.
Arguments SplitS {_} _ _.

Lemma trunk_splitterS (trunk: BTrunk) (P P': forall path: BPath, BTContains trunk path -> SProp): (forall path: BPath, forall contains: BTContains trunk path, SumBoolS (P path contains) (P' path contains)) -> SplitS (fun path: BPath => existsSS contains: BTContains trunk path, P path contains) (forall path: BPath, forall contains: BTContains trunk path, P' path contains).
Proof.
  intro split.
  induction trunk; simpl in *.
  + right.
    intros path [ ].
  + specialize (IHtrunk1 (fun path => P (bfirst path)) (fun path => P' (bfirst path)) (fun path => split (bfirst path))).
    destruct IHtrunk1 as [ path1 IHtrunk1 | IHtrunk1 ]; [ apply split_exists with (bfirst path1); destruct IHtrunk1 as [ contains1 IHtrunk1 ]; exists contains1; assumption | ].
    specialize (IHtrunk2 (fun path => P (bsecond path)) (fun path => P' (bsecond path)) (fun path => split (bsecond path))).
    destruct IHtrunk2 as [ path2 IHtrunk2 | IHtrunk2 ]; [ apply split_exists with (bsecond path2); destruct IHtrunk2 as [ contains2 IHtrunk2 ]; exists contains2; assumption | ].
    destruct head.
    - right.
      intros path contains.
      destruct path as [ | path | path ].
      * destruct contains.
      * apply IHtrunk1.
      * apply IHtrunk2.
    - specialize (split bend trueS).
      destruct split as [ p | p' ]; [ apply split_exists with bend; exists trueS; assumption | ].
      right.
      intros path contains.
      destruct path as [ | path | path ].
      * apply p'.
      * apply IHtrunk1.
      * apply IHtrunk2.
Qed.

Lemma finite_splitterS {A: Type} `{Finite A} (P P': A -> SProp): (forall a: A, SumBoolS (P a) (P' a)) -> SplitS (fun a: A => P a) (forall a: A, P' a).
Proof.
  intro split.
  destruct (trunk_splitterS (sftrunk A) (fun path contains => P (fpath A path contains)) (fun path contains => P' (fpath A path contains))) as [ path p | p' ].
  + intros path contains.
    apply split.
  + apply split_exists with (fpath A path p.(proj1_exSS)).
    exact p.(proj2_exSS).
  + right.
    intro a.
    specialize (p' (scpath a) (sfcontains a)).
    destruct (fpath_scpath_eq a).
    assumption.
Qed.
Lemma finite_splitterS' {A: Type} `{Finite A} (P P': A -> SProp): (forall a: A, SumBoolS (P a) (P' a)) -> SplitS (fun a: A => P' a) (forall a: A, P a).
Proof.
  intro split.
  destruct (finite_splitterS P' P) as [ a p' | p ].
  + intro a.
    specialize (split a).
    destruct split as [ p | p' ].
    - right.
      assumption.
    - left.
      assumption.
  + apply split_exists with a.
    assumption.
  + right.
    assumption.
Qed.



(* The following demonstrate that many common types belong to various cardinalities. *)
#[local] #[refine] Instance Empty_SubCountable: SubCountable Empty :=
{ scpath e := match e with end;
}.
Proof.
  intros [ ].
Qed.
#[local] #[refine] Instance Empty_SubFinite: SubFinite Empty :=
{ sftrunk := bleaf }.
Proof.
  intros [].
Defined.

#[local] #[refine] Instance unit_SubCountable: SubCountable unit :=
{ scpath _ := bend }.
Proof.
  intros [ ] [ ] _.
  reflexivity.
Defined.
#[local] #[refine] Instance unit_SubFinite: SubFinite unit :=
{ sftrunk := bbranch opresent bleaf bleaf }.
Proof.
  intros [ ].
  constructor.
Defined.
#[local] #[refine] Instance unit_Finite: Finite unit :=
{ fpath _ _ := tt }.
Proof.
  intros path contains.
  destruct path; destruct contains.
  reflexivity.
Qed.

#[local] #[refine] Instance Sign_SubCountable: SubCountable Sign :=
{ scpath (sign: Sign) := match sign with negative => bfirst bend | positive => bsecond bend end }.
Proof.
  intros sign sign' e.
  destruct sign; destruct sign'; inversion_clear e; reflexivity.
Defined.

#[local] #[refine] Instance option_SubCountable (T: Type) `{SubCountable T}: SubCountable (option T) :=
{ scpath o := match o with None => bend | Some t => bfirst (scpath t) end }.
Proof.
  intros [ t | ] [ t' | ] e; inversion e; clear e; try reflexivity.
  apply scpath_inj in H1.
  f_equal.
  assumption.
Defined.
#[local] #[refine] Instance option_SubFinite (T: Type) `{SubFinite T}: SubFinite (option T) :=
{ sftrunk := bbranch opresent (sftrunk T) bleaf }.
Proof.
  intros [ t | ]; simpl; try constructor.
  apply sfcontains.
Defined.
#[local] #[refine] Instance option_Finite (T: Type) `{Finite T}: Finite (option T) :=
{ fpath path := match path with
                | bend => fun _ => None
                | bfirst path => fun contains => Some (fpath T path contains)
                | bsecond path => falseSe
                end
}.
Proof.
  intros path contains.
  destruct path; simpl in *.
  + reflexivity.
  + rewrite <- fpath_eq.
    reflexivity.
  + destruct contains.
Qed.

#[local] #[refine] Instance sum_SubCountable (L R: Type) `{SubCountable L} `{SubCountable R}: SubCountable (sum L R) :=
{ scpath s := match s with inl l => bfirst (scpath l) | inr r => bsecond (scpath r) end }.
Proof.
  intros [ l | r ] [ l' | r' ] e; inversion e; clear e; apply scpath_inj in H2; f_equal; assumption.
Defined.
#[local] #[refine] Instance sum_SubFinite (L R: Type) `{sfL: SubFinite L} `{sfR: SubFinite R}: SubFinite (sum L R) :=
{ sftrunk := bbranch oabsent (sftrunk L) (sftrunk R) }.
Proof.
  intros [ l | r ]; apply sfcontains.
Defined.
#[local] #[refine] Instance sum_Finite (L R: Type) `{Finite L} `{Finite R}: Finite (sum L R) :=
{ fpath path := match path with
                | bend => falseSe
                | bfirst path => fun contains => inl (fpath L path contains)
                | bsecond path => fun contains => inr (fpath R path contains)
                end
}.
Proof.
  intros path contains.
  destruct path; simpl in *.
  + destruct contains.
  + rewrite <- fpath_eq.
    reflexivity.
  + rewrite <- fpath_eq.
    reflexivity.
Qed.

#[local] #[refine] Instance prod_SubCountable (A B: Type) `{SubCountable A} `{SubCountable B}: SubCountable (prod A B) :=
{ scpath ab := bpath_pair (scpath (fst ab)) (scpath (snd ab)) }.
Proof.
  intros [ a b ] [ a' b' ] e; simpl in e.
  apply bpath_pair_inj in e.
  destruct e as [ ea eb ].
  apply scpath_inj in ea.
  destruct ea.
  apply scpath_inj in eb.
  destruct eb.
  reflexivity.
Defined.
#[local] #[refine] Instance prod_SubFinite (A: Type) (B: Type) `{SubFinite A} `{SubFinite B}: SubFinite (prod A B) :=
{ sftrunk := btrunk_pair (sftrunk A) (fun _ _ => sftrunk B) }.
Proof.
  intros [ a b ].
  apply btcontains_pair; apply sfcontains.
Defined.
#[local] #[refine] Instance prod_Finite (A: Type) (B: Type) `{Finite A} `{Finite B}: Finite (prod A B) :=
{ fpath path contains := pair (fpath A (bpath_fst path) (btcontains_fst contains)) (fpath B (bpath_snd path) (btcontains_snd contains)) }.
Proof.
  simpl.
  intros path contains.
  rewrite <- fpath_eq.
  rewrite <- fpath_eq.
  erewrite <- bpath_pair_fst_snd; try eassumption.
  reflexivity.
Qed.

#[local] #[refine] Instance sigT_SubCountable (A: Type) (B: A -> Type) `{SubCountable A} `{forall a: A, SSet (B a)} `{forall a: A, SubCountable (B a)}: SubCountable (sigT B) :=
{ scpath s := bpath_pair (scpath (projT1 s)) (scpath (projT2 s)) }.
Proof.
  intros [ a b ] [ a' b' ] e; simpl in e.
  apply bpath_pair_inj in e.
  destruct e as [ ea eb ].
  apply scpath_inj in ea.
  destruct ea.
  apply scpath_inj in eb.
  destruct eb.
  reflexivity.
Defined.
#[local] #[refine] Instance sigT_SubFinite (A: Type) (B: A -> Type) {fA: Finite A} {sfB: forall a: A, SubFinite (B a)}: SubFinite (sigT B) :=
{ sftrunk := btrunk_pair (sftrunk A) (fun path contains => sftrunk (B (fpath A path contains))) }.
Proof.
  intros [ a b ].
  eapply btcontains_pair.
  simpl.
  rewrite <- fpath_scpath_eq.
  apply sfcontains.
Defined.
#[local] #[refine] Instance sigT_Finite (A: Type) (B: A -> Type) {fA: Finite A} {fB: forall a: A, Finite (B a)}: Finite (sigT B) :=
{ fpath path contains := existT B (fpath A (bpath_fst path) (btcontains_fst contains)) (fpath (B (fpath A (bpath_fst path) (btcontains_fst contains))) (bpath_snd path) (btcontains_snd contains)) }.
Proof.
  simpl.
  intros path contains.
  rewrite <- fpath_eq.
  rewrite <- fpath_eq.
  erewrite <- bpath_pair_fst_snd; try eassumption.
  reflexivity.
Qed.

#[local] #[refine] Instance Box_SubCountable (P: SProp): SubCountable (Box P) :=
{ scpath b := bend }.
Proof.
  intros [ p ] [ p' ] _.
  reflexivity.
Defined.
#[local] #[refine] Instance Box_SubFinite (P: SProp) `{DecidableS P}: SubFinite (Box P) :=
{ sftrunk := bbranch (match decidableS P with
                      | sbleftS _ => opresent
                      | sbrightS _ => oabsent
                      end)
                     bleaf
                     bleaf
}.
Proof.
  intros [ p ].
  destruct (decidableS P) as [ _ | np ].
  - split.
  - destruct (np p).
Defined.
#[local] #[refine] Instance Box_Finite (P: SProp) `{DecidableS P}: Finite (Box P) :=
{ fpath path := match path with
                | bend => match decidableS P as d return PresentS (match d with sbleftS _ => opresent | sbrightS _ => oabsent end) -> Box P with
                          | sbleftS p => fun _ => box p
                          | sbrightS _ => falseSe
                          end
                | bfirst _ => falseSe
                | bsecond _ => falseSe
                end
}.
Proof.
  simpl.
  intros path contains.
  destruct path; try destruct contains.
  reflexivity.
Qed.

#[local] #[refine] Instance sigSdT_SubCountable (A: Type) (P: A -> SProp) (B: forall a: A, P a -> Type) {scP: SubCountableS P} {scB: forall a: A, forall p: P a, SubCountable (B a p)}: SubCountable (sigSdT P B) :=
{ scpath s := bpath_pair (scpathS s.(proj1_sigSdT) s.(proj2_sigSdT)) (scpath s.(proj3_sigSdT)) }.
Proof.
  intros s [ a' p' b' ].
  cbn.
  intro e.
  apply bpath_pair_inj in e.
  destruct e as [ e e' ].
  apply scpathS_inj in e.
  destruct e.
  apply scpath_inj in e'.
  destruct e'.
  reflexivity.
Defined.
#[local] #[refine] Instance sigSdT_SubFinite (A: Type) (P: A -> SProp) (B: forall a: A, P a -> Type) {fP: FiniteS P} {sfB: forall a: A, forall p: P a, SubFinite (B a p)}: SubFinite (sigSdT P B) :=
{ sftrunk := btrunk_pair (sftrunkS P) (fun path contains => sftrunk (B (fpathS P path contains) (fpathSP P path contains))) }.
Proof.
  intro s.
  apply btcontains_pair with (sfcontainsS s.(proj1_sigSdT) s.(proj2_sigSdT)).
  generalize (fpathSP P (scpathS s.(proj1_sigSdT) s.(proj2_sigSdT)) (sfcontainsS s.(proj1_sigSdT) s.(proj2_sigSdT))).
  rewrite <- fpathS_scpathS_eq.
  intro p.
  apply sfcontains.
Defined.
#[local] #[refine] Instance sigSdT_Finite (A: Type) (P: A -> SProp) (B: forall a: A, P a -> Type) {fP: FiniteS P} {fB: forall a: A, forall p: P a, Finite (B a p)}: Finite (sigSdT P B) :=
{ fpath path contains := @existSdT A P B (fpathS P (bpath_fst path) (btcontains_fst contains)) (fpathSP P (bpath_fst path) (btcontains_fst contains)) (fpath (B (fpathS P (bpath_fst path) (btcontains_fst contains)) (fpathSP P (bpath_fst path) (btcontains_fst contains))) (bpath_snd path) (btcontains_snd contains)) }.
Proof.
  simpl.
  intros path contains.
  rewrite <- fpathS_eq.
  rewrite <- fpath_eq.
  erewrite <- bpath_pair_fst_snd; try eassumption.
  reflexivity.
Qed.



(* Part 1.5: General Recursion
 * The termination of our algorithm is based on co-well-founded (tail) recursion.
 *)
Inductive CoAcc {T: Type} {R: T -> T -> Prop} | {t: T}: Prop
:= coacc: (forall t': T, R t t' -> CoAcc (t := t')) -> CoAcc.
Arguments CoAcc {_} _ _.

Lemma option_cwf {T: Type} (D: T -> Prop) (R: T -> T -> Prop) (o: option T): (forall t: T, D t -> CoAcc R t) -> (match o with None => True | Some t => CoAcc R t end) -> CoAcc (fun o o' => match o, o' with None, Some t' => D t' | Some t, Some t' => R t t' | _, None => False end) o.
Proof.
  intros d_cwf o_cwf.
  destruct o.
  + induction o_cwf as [ t _ IHt ].
    constructor.
    intros o' r.
    destruct o' as [ t' | ]; [ | destruct r ].
    apply IHt.
    assumption.
  + clear o_cwf.
    constructor.
    intros o' r.
    destruct o' as [ t' | ]; [ | destruct r ].
    apply d_cwf in r.
    induction r as [ t' _ IHt' ].
    constructor.
    intros o'' r'.
    destruct o'' as [ t'' | ]; [ | destruct r' ].
    apply IHt'.
    assumption.
Qed.



(* Part 1.6: Data-Structures *)

(* The key data-structure we use is binary trees, which are accessed using binary paths.
 * These binary trees are parameterized by a property that specifies what keys are allowed to occur at what path-locations within the tree.
 * This conncection between keys and paths enable efficient implementations of, for example, partial maps from subcountable sets.
 *)
Record BEntry {K: Type} {V: K -> Type} {P: K -> SProp}: Type := bentry
{ bekey: K;
  bekeyP: P bekey;
  bevalue: V bekey;
}.
Arguments BEntry : clear implicits.

Inductive BTree {K: Type} {V: K -> Type} | {P: BPath -> K -> SProp}: Type
:= bempty
 | bnode (head: option (BEntry K V (P bend))) (first: BTree (P := fun path => P (bfirst path))) (second: BTree (P := fun path => P (bsecond path))).
Arguments BTree : clear implicits.

Definition BContainsPath {K: Type} {V: K -> Type}: forall {P: BPath -> K -> SProp}, BTree K V P -> BPath -> SProp
:= fix BContainsPath {P: BPath -> K -> SProp} (tree: BTree K V P): BPath -> SProp
:= match tree with
   | bempty => fun _ => FalseS
   | bnode head first second => fun path => match path with
                                            | bend => optione FalseS (fun _ => TrueS) head
                                            | bfirst path => BContainsPath first path
                                            | bsecond path => BContainsPath second path
                                            end
   end.

Definition btree_trunk {K: Type} {V: K -> Type}: forall {P: BPath -> K -> SProp}, BTree K V P -> BTrunk
:= fix btree_trunk {P: BPath -> K -> SProp} (tree: BTree K V P): BTrunk
:= match tree with
   | bempty => bleaf
   | bnode entry tree1 tree2 => bbranch (match entry with None => oabsent | Some _ => opresent end) (btree_trunk tree1) (btree_trunk tree2)
   end.

Lemma btree_trunk_contains {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} {tree: BTree K V P} {path: BPath}: BContainsPath tree path -> BTContains (btree_trunk tree) path.
Proof.
  revert path; induction tree; intro path; simpl; try trivial.
  intro contains.
  destruct path.
  + destruct head.
    - constructor.
    - assumption.
  + apply IHtree1.
    assumption.
  + apply IHtree2.
    assumption.
Qed.
Lemma btree_trunk_contains' {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} {tree: BTree K V P} {path: BPath}: BTContains (btree_trunk tree) path -> BContainsPath tree path.
Proof.
  revert path; induction tree; intro path; simpl; try trivial.
  intro contains.
  destruct path.
  + destruct head.
    - constructor.
    - assumption.
  + apply IHtree1.
    assumption.
  + apply IHtree2.
    assumption.
Qed.

#[local] Instance BContainsPath_DecidableS {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} (tree: BTree K V P) (path: BPath): DecidableS (BContainsPath tree path).
Proof.
  revert path; induction tree; intro path.
  + right.
    destruct path; intros [ ].
  + destruct path; simpl; try auto.
    destruct head; simpl; apply _.
Qed.
#[local] #[refine] Instance BContainsPath_SubCountableS {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} (tree: BTree K V P): SubCountableS (BContainsPath tree) :=
{ scpathS path _ := path }.
Proof.
  trivial.
Defined.
#[local] #[refine] Instance BContainsPath_SubFiniteS {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} (tree: BTree K V P): SubFiniteS (BContainsPath tree) :=
{ sftrunkS := btree_trunk tree }.
Proof.
  apply (@btree_trunk_contains).
Defined.
#[local] #[refine] Instance BContainsPath_FiniteS {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} (tree: BTree K V P): FiniteS (BContainsPath tree) :=
{ fpathS path _ := path }.
Proof.
+ apply (@btree_trunk_contains').
+ reflexivity.
Qed.

Definition bget_contained {K: Type} {V: K -> Type}: forall {P: BPath -> K -> SProp}, forall tree: BTree K V P, forall path: BPath, BContainsPath tree path -> BEntry K V (P path)
:= fix bget_contained {P: BPath -> K -> SProp} (tree: BTree K V P): forall path: BPath, BContainsPath tree path -> BEntry K V (P path)
:= match tree with
   | bempty => fun _ => falseSe
   | bnode head first second => fun path => match path with
                                            | bend => match head with
                                                      | Some head => fun _ => head
                                                      | None => falseSe
                                                      end
                                            | bfirst path => bget_contained first path
                                            | bsecond path => bget_contained second path
                                            end
   end.

Definition bget {K: Type} {V: K -> Type}: forall {P: BPath -> K -> SProp}, forall tree: BTree K V P, forall path: BPath, option (BEntry K V (P path))
:= fix bget {P: BPath -> K -> SProp} (tree: BTree K V P): forall path: BPath, option (BEntry K V (P path))
:= match tree with
   | bempty => fun _ => None
   | bnode head first second => fun path => match path with
                                            | bend => head
                                            | bfirst path => bget first path
                                            | bsecond path => bget second path
                                            end
   end.

Lemma bget_contains {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} (tree: BTree K V P) (path: BPath): match bget tree path with None => BContainsPath tree path -> False | Some entry => existsSP contains: BContainsPath tree path, bget_contained tree path contains = entry end.
Proof.
  revert path; induction tree; intro path; simpl.
  + apply falseS_false.
  + destruct path.
    - destruct head.
      * exists trueS.
        reflexivity.
      * apply falseS_false.
    - apply IHtree1.
    - apply IHtree2.
Qed.

Definition bsingleton {K: Type} {V: K -> Type}: forall {P: BPath -> K -> SProp}, forall path: BPath, BEntry K V (P path) -> BTree K V P
:= fix bsingleton {P: BPath -> K -> SProp} (path: BPath): BEntry K V (P path) -> BTree K V P
:= match path with
   | bend => fun entry => bnode (Some entry) bempty bempty
   | bfirst path => fun entry => bnode None (bsingleton path entry) bempty
   | bsecond path => fun entry => bnode None bempty (bsingleton path entry)
   end.

Lemma bsingleton_contains {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} (path: BPath) (entry: BEntry K V (P path)): BContainsPath (bsingleton path entry) path.
Proof.
  revert P entry; induction path; intros P entry; simpl.
  + constructor.
  + apply IHpath.
  + apply IHpath.
Qed.
Lemma bcontains_singleton {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} {path: BPath} {entry: BEntry K V (P path)} {path': BPath} (contains': BContainsPath (bsingleton path entry) path'): eqS path path'.
Proof.
  revert P entry path' contains'; induction path; intros P entry path' contains'; simpl in contains'; destruct path'; try (destruct contains'; fail).
  * reflexivity.
  * apply IHpath in contains'.
    destruct contains'.
    reflexivity.
  * apply IHpath in contains'.
    destruct contains'.
    reflexivity.
Qed.
Lemma bget_contains_singleton {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} (path: BPath) (entry: BEntry K V (P path)) (path': BPath) (contains': BContainsPath (bsingleton path entry) path'): bget_contained (bsingleton path entry) path' contains' = convert (bcontains_singleton contains') (fun path => BEntry K V (P path)) entry.
Proof.
  destruct (eqS_eq (bcontains_singleton contains')).
  rewrite convert_id.
  rename contains' into contains.
  revert P entry contains; induction path; simpl; intros P entry contains.
  * reflexivity.
  * exact (IHpath _ entry contains).
  * exact (IHpath _ entry contains).
Qed.

(* BExtends is a non-strict property because it is often used for termination, and Rocq can only structurally recurse on non-strict propositions.
 * It indicates that the latter tree is the former tree extended with the given entry added at or replacing the entry at the given path-location.
 *)
Inductive BExtends {K: Type} {V: K -> Type} | {P: BPath -> K -> SProp}: BTree K V P -> forall path: BPath, BEntry K V (P path) -> BTree K V P -> Prop
:= beempty (path: BPath) (entry: BEntry K V (P path)): BExtends bempty path entry (bsingleton path entry)
 | beend (entry: BEntry K V (P bend)) (head: option (BEntry K V (P bend))) (tree1: BTree K V (fun path => P (bfirst path))) (tree2: BTree K V (fun path => P (bsecond path))): BExtends (bnode head tree1 tree2) bend entry (bnode (Some entry) tree1 tree2)
 | befirst (path: BPath) (entry: BEntry K V (P (bfirst path))) (head: option (BEntry K V (P bend))) (tree1 tree1': BTree K V (fun path => P (bfirst path))) (tree2: BTree K V (fun path => P (bsecond path))): BExtends tree1 path entry tree1' -> BExtends (bnode head tree1 tree2) (bfirst path) entry (bnode head tree1' tree2)
 | besecond (path: BPath) (entry: BEntry K V (P (bsecond path))) (head: option (BEntry K V (P bend))) (tree1: BTree K V (fun path => P (bfirst path))) (tree2 tree2': BTree K V (fun path => P (bsecond path))): BExtends tree2 path entry tree2' -> BExtends (bnode head tree1 tree2) (bsecond path) entry (bnode head tree1 tree2').

Lemma bextends_contains {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} {tree: BTree K V P} {path: BPath} {entry: BEntry K V (P path)} {tree': BTree K V P}: BExtends tree path entry tree' -> forall {path': BPath}, BContainsPath tree path' -> BContainsPath tree' path'.
Proof.
  intros extends.
  induction extends; simpl; intros path' contains.
  + destruct contains.
  + destruct path'; try assumption.
    constructor.
  + destruct path'; auto.
  + destruct path'; auto.
Qed.
Lemma bextends_contains_path {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} {tree: BTree K V P} {path: BPath} {entry: BEntry K V (P path)} {tree': BTree K V P}: BExtends tree path entry tree' -> BContainsPath tree' path.
Proof.
  intros extends.
  induction extends; simpl.
  + apply bsingleton_contains.
  + constructor.
  + assumption.
  + assumption.
Qed.
Lemma bcontains_extends {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} {tree: BTree K V P} {path: BPath} {entry: BEntry K V (P path)} {tree': BTree K V P}: BExtends tree path entry tree' -> forall {path': BPath}, BContainsPath tree' path' -> OrS (eqS path path') (BContainsPath tree path').
Proof.
  intro extends.
  induction extends; simpl; intros path' contains'.
  + left.
    apply bcontains_singleton in contains'.
    assumption.
  + destruct path'; try (right; assumption).
    left.
    reflexivity.
  + destruct path'.
    - right.
      assumption.
    - apply IHextends in contains'.
      destruct contains' as [ e | contains' ].
      * left.
        destruct e.
        reflexivity.
      * right.
        assumption.
    - right.
      assumption.
  + destruct path'.
    - right.
      assumption.
    - right.
      assumption.
    - apply IHextends in contains'.
      destruct contains' as [ e | contains' ].
      * left.
        destruct e.
        reflexivity.
      * right.
        assumption.
Qed.
Lemma bcontains_extends_neq {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} {tree: BTree K V P} {path: BPath} {entry: BEntry K V (P path)} {tree': BTree K V P}: BExtends tree path entry tree' -> forall {path': BPath}, BContainsPath tree' path' -> (eqS path path' -> FalseS) -> BContainsPath tree path'.
Proof.
  intros extends path' contains' ne.
  apply bcontains_extends with path' in extends; try assumption.
  destruct extends; try assumption.
  exfalso.
  apply falseS_false.
  apply ne.
  assumption.
Qed.
Lemma bget_contained_extends_eq {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} {tree: BTree K V P} {path: BPath} {entry: BEntry K V (P path)} {tree': BTree K V P} (extends: BExtends tree path entry tree') (contains': BContainsPath tree' path): bget_contained tree' path contains' = entry.
Proof.
  induction extends; simpl in *; try auto.
  rewrite bget_contains_singleton.
  rewrite convert_id.
  reflexivity.
Qed.
Lemma bget_contained_extends_neq {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} {tree: BTree K V P} {path: BPath} {entry: BEntry K V (P path)} {tree': BTree K V P} (extends: BExtends tree path entry tree') {path': BPath} (ne: eqS path path' -> FalseS) (contains': BContainsPath tree' path'): bget_contained tree' path' contains' = bget_contained tree path' (bcontains_extends_neq extends contains' ne).
Proof.
  generalize (bcontains_extends_neq extends contains' ne).
  revert path' contains' ne; induction extends; intros path' contains' ne contains; simpl in *; try auto.
  + destruct contains.
  + destruct path'; try reflexivity.
    exfalso.
    apply falseS_false.
    apply ne.
    reflexivity.
  + destruct path'; try reflexivity.
    apply IHextends.
    intro e.
    apply ne.
    destruct e.
    reflexivity.
  + destruct path'; try reflexivity.
    apply IHextends.
    intro e.
    apply ne.
    destruct e.
    reflexivity.
Qed.

Lemma bextends_cwf
      (trunk: BTrunk)
      {K: Type}
      {V: K -> Type}
      {P: BPath -> K -> SProp}
      (D: forall path: BPath, BEntry K V (P path) -> Prop)
      (R: forall path: BPath, BEntry K V (P path) -> BEntry K V (P path) -> Prop)
      (tree: BTree K V P)
    : (forall path: BPath, forall entry: BEntry K V (P path), D path entry -> CoAcc (R path) entry)
   -> (forall path: BPath, forall contains: BContainsPath tree path, CoAcc (R path) (bget_contained tree path contains))
   -> CoAcc (fun tree tree' => existsTSP path: BPath,
                               BTContains trunk path
                             & exists2 entry': BEntry K V (P path),
                               BExtends tree path entry' tree'
                             & match bget tree path with
                               | None => D path entry'
                               | Some entry => R path entry entry'
                               end)
            tree.
Proof.
  revert P D R tree; induction trunk; intros P D R tree d_cwf tree_cwf; simpl in *.
  + constructor.
    intros _ [ _ [ ] _ ].
  + rename head into root.
    match goal with |- CoAcc ?R' _ => assert (forall head, optione True (CoAcc (R bend)) head -> forall tree1, (forall path contains, CoAcc (R (bfirst path)) (bget_contained tree1 path contains)) -> forall tree2, (forall path contains, CoAcc (R (bsecond path)) (bget_contained tree2 path contains)) -> CoAcc R' (bnode head tree1 tree2)) as bnode_cwf end.
    - intros head head_cwf.
      induction (option_cwf (D bend) (R bend) head) as [ head _ IHhead ]; try auto.
      intros tree1 tree1_cwf.
      specialize (IHtrunk1 (fun path => P (bfirst path)) (fun path => D (bfirst path)) (fun path => R (bfirst path)) tree1 (fun path => d_cwf (bfirst path)) tree1_cwf).
      induction IHtrunk1 as [ tree1 _ IHtree1 ].
      intros tree2 tree2_cwf.
      specialize (IHtrunk2 (fun path => P (bsecond path)) (fun path => D (bsecond path)) (fun path => R (bsecond path)) tree2 (fun path => d_cwf (bsecond path)) tree2_cwf).
      induction IHtrunk2 as [ tree2 _ IHtree2 ].
      constructor.
      intros tree' [ path incl [ entry' extends r ] ].
      inversion_hset extends; simpl in r.
      * clear H.
        apply IHhead; try assumption.
        simpl.
        destruct head as [ entry | ].
        ** destruct head_cwf as [ head_cwf ].
           apply head_cwf.
           assumption.
        ** apply d_cwf.
           assumption.
      * clear H4; rename path0 into path; rename H6 into extends.
        apply IHtree1; try assumption.
        ** exists path; try assumption.
           exists entry'; assumption.
        ** intros path' contains'.
           destruct (decidableS (eqS path path')) as [ e | ne ].
           *** destruct (eqS_eq e); clear e.
               erewrite bget_contained_extends_eq; try eassumption.
               pose proof (bget_contains tree1 path) as contains1.
               destruct (bget tree1 path) as [ entry | ].
               **** destruct contains1 as [ contains1 e ].
                    destruct e.
                    specialize (tree1_cwf _ contains1).
                    destruct tree1_cwf as [ entry_cwf ].
                    apply entry_cwf.
                    assumption.
               **** apply d_cwf.
                    assumption.
           *** rewrite bget_contained_extends_neq with (extends := extends) (ne := ne).
               apply tree1_cwf.
      * clear H4; rename path0 into path; rename H6 into extends.
        apply IHtree2; try assumption.
        ** exists path; try assumption.
           exists entry'; assumption.
        ** intros path' contains'.
           destruct (decidableS (eqS path path')) as [ e | ne ].
           *** destruct (eqS_eq e); clear e.
               erewrite bget_contained_extends_eq; try eassumption.
               pose proof (bget_contains tree2 path) as contains2.
               destruct (bget tree2 path) as [ entry | ].
               **** destruct contains2 as [ contains2 e ].
                    destruct e.
                    specialize (tree2_cwf _ contains2).
                    destruct tree2_cwf as [ entry_cwf ].
                    apply entry_cwf.
                    assumption.
               **** apply d_cwf.
                    assumption.
           *** rewrite bget_contained_extends_neq with (extends := extends) (ne := ne).
               apply tree2_cwf.
    - destruct tree.
      * constructor.
        intros tree' [ path contains [ entry extends r ] ].
        inversion_hset extends.
        destruct path; simpl; apply bnode_cwf; simpl in *; try auto.
        ** intros path' contains'.
           rewrite bget_contains_singleton.
           destruct (eqS_eq (bcontains_singleton contains')).
           rewrite convert_id.
           apply d_cwf.
           assumption.
        ** intros path' contains'.
           rewrite bget_contains_singleton.
           destruct (eqS_eq (bcontains_singleton contains')).
           rewrite convert_id.
           apply d_cwf.
           assumption.
      * apply bnode_cwf.
        ** specialize (tree_cwf bend).
           destruct head; simpl in *; try apply tree_cwf; constructor.
        ** intros path contains.
           specialize (tree_cwf (bfirst path) contains).
           assumption.
        ** intros path contains.
           specialize (tree_cwf (bsecond path) contains).
           assumption.
Qed.

(* bupdate is the key function for conceptually mutating a binary tree.
 * One provides it with a tree, a path, and an update to be applied at that location within the tree.
 * The update itself takes an indication as to whether there was or was not already an entry at that location,
 * and then it returns either the entry to replace it with, or an indication to make no change, or an indication that the update is incompatible with the preexisting entry.
 * bupdate then either returns the corresponding updated tree, or an indication that no change was made to the tree, or an indication that the update is incompatible with the tree.
 *)
Definition bupdate {K: Type} {V: K -> Type}: forall {P: BPath -> K -> SProp}, forall tree: BTree K V P, forall path: BPath, (SumBoolS (BContainsPath tree path) (BContainsPath tree path -> FalseS) -> option (option (BEntry K V (P path)))) -> option (option (BTree K V P))
:= fix bupdate {P: BPath -> K -> SProp} (tree: BTree K V P): forall path: BPath, (SumBoolS (BContainsPath tree path) (BContainsPath tree path -> FalseS) -> option (option (BEntry K V (P path)))) -> option (option (BTree K V P))
:= match tree as tree return forall path: BPath, (DeciderS (BContainsPath tree path) -> option (option (BEntry K V (P path)))) -> option (option (BTree K V P)) with
   | bempty => fun path update => option_map (option_map (bsingleton path)) (update (sbrightS (fun f => f)))
   | bnode entry tree1 tree2 => fun path => match path as path return (DeciderS (BContainsPath (bnode entry tree1 tree2) path) -> option (option (BEntry K V (P path)))) -> option (option (BTree K V P)) with
                                            | bend => match entry as entry return (DeciderS (BContainsPath (bnode entry tree1 tree2) bend) -> option (option (BEntry K V (P bend)))) -> option (option (BTree K V P)) with
                                                      | None => fun update => option_map (option_map (fun entry => bnode (Some entry) tree1 tree2)) (update (sbrightS (fun f => f)))
                                                      | Some _ => fun update => option_map (option_map (fun entry => bnode (Some entry) tree1 tree2)) (update (sbleftS trueS))
                                                      end
                                            | bfirst path => fun update => option_map (option_map (fun tree1 => bnode entry tree1 tree2)) (bupdate tree1 path update)
                                            | bsecond path => fun update => option_map (option_map (fun tree2 => bnode entry tree1 tree2)) (bupdate tree2 path update)
                                            end
   end.

Lemma bupdate_extends
      {K: Type}
      {V: K -> Type}
      {P: BPath -> K -> SProp}
      (tree: BTree K V P)
      (path: BPath)
      (update: DeciderS (BContainsPath tree path) -> option (option (BEntry K V (P path))))
      (D: BEntry K V (P path) -> Prop)
      (E: BContainsPath tree path -> Prop)
      (I: BContainsPath tree path -> Prop)
      (R: BContainsPath tree path -> BEntry K V (P path) -> Prop)
    : (forall ncontains: BContainsPath tree path -> FalseS, match update (sbrightS ncontains) with None => False | Some None => False | Some (Some entry) => D entry end)
   -> (forall contains: BContainsPath tree path, match update (sbleftS contains) with None => E contains | Some None => I contains | Some (Some entry') => R contains entry' end)
   -> match bupdate tree path update with
      | None => existsSP contains: BContainsPath tree path,
                E contains
      | Some None => existsSP contains: BContainsPath tree path,
                     I contains
      | Some (Some tree') => exists2 entry': BEntry K V (P path),
                             BExtends tree path entry' tree'
                           & ((BContainsPath tree path -> FalseS) -> D entry')
                          /\ (forall contains: BContainsPath tree path, R contains entry')
      end.
Proof.
  revert path update D E I R; induction tree; simpl; intros path update D E I R update_none update_some.
  + specialize (update_none (fun f => f)).
    destruct (update (sbrightS (fun f => f))) as [ [ entry' | ] | ]; [ | destruct update_none | destruct update_none ]; simpl.
    exists entry'; try apply beempty.
    split; [ | intros [ ] ].
    intros _.
    assumption.
  + destruct path.
    - destruct head as [ entry | ].
      * specialize (update_some trueS).
        simpl in *.
        destruct (update (sbleftS trueS)) as [ [ entry' | ] | ]; simpl.
        ** exists entry'; try apply beend.
           split; [ intro f; destruct (f trueS) | ].
           intro contains.
           assumption.
        ** exists trueS.
           assumption.
        ** exists trueS.
           assumption.
      * specialize (update_none (fun f => f)).
        simpl in *.
        destruct (update (sbrightS (fun f => f))) as [ [ entry | ] | ]; [ | destruct update_none | destruct update_none ]; simpl.
        exists entry; try apply beend.
        split; [ | intros [ ] ].
        intros _.
        assumption.
    - specialize (IHtree1 path update D E I R update_none update_some).
      destruct (bupdate tree1 path update) as [ [ tree1' | ] | ]; simpl; try assumption.
      destruct IHtree1 as [ entry' extends IHtree1 ].
      exists entry'; try (apply befirst; assumption).
      assumption.
    - specialize (IHtree2 path update D E I R update_none update_some).
      destruct (bupdate tree2 path update) as [ [ tree2' | ] | ]; simpl; try assumption.
      destruct IHtree2 as [ entry' extends IHtree2 ].
      exists entry'; try (apply besecond; assumption).
      assumption.
Qed.

Definition bentries' {K: Type} {V: K -> Type} {P: BPath -> K -> SProp}: forall f: BPath -> BPath, BTree K V (compose f P) -> list (sigT (fun path => BEntry K V (P path)))
:= fix bentries' (f: BPath -> BPath) (tree: BTree K V (compose f P)): list (sigT (fun path => BEntry K V (P path)))
:= match tree with
   | bempty => nil
   | bnode head tree1 tree2 => match head with
                               | None => app (bentries' (compose bfirst f) tree1) (bentries' (compose bsecond f) tree2)
                               | Some entry => cons (existT _ (f bend) entry) (app (bentries' (compose bfirst f) tree1) (bentries' (compose bsecond f) tree2))
                               end
   end.
Definition bentries {K: Type} {V: K -> Type} {P: BPath -> K -> SProp}: BTree K V P -> list (sigT (fun path => BEntry K V (P path)))
:= bentries' (fun path => path).

Definition BTreeContains {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} (tree: BTree K V P) (path: BPath) (entry: BEntry K V (P path)): SProp
:= existsSS contains: BContainsPath tree path, eqS (bget_contained tree path contains) entry.

Lemma btreecontains_get_contained {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} (tree: BTree K V P) (path: BPath) (contains: BContainsPath tree path): BTreeContains tree path (bget_contained tree path contains).
Proof.
  exists contains.
  reflexivity.
Qed.

Lemma bentries_contains' {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} {f: BPath -> BPath} {tree: BTree K V (compose f P)}: forall path: BPath, forall contains: BContainsPath tree path, ListContains (existT _ (f path) (bget_contained tree path contains)) (bentries' f tree).
Proof.
  remember (btree_trunk tree) as trunk.
  revert P f tree Heqtrunk.
  induction trunk as [ | root trunk1 IHtrunk1 trunk2 IHtrunk2 ]; intros P f tree etrunk path contains; destruct tree as [ | head tree1 tree2 ]; inversion_hset etrunk; simpl in *.
  + destruct contains.
  + destruct path.
    - destruct head as [ entry | ]; destruct contains.
      apply lchead.
    - destruct head as [ entry | ].
      * apply lctail.
        apply contains_app_l.
        specialize (IHtrunk1 _ (compose bfirst f) tree1 eq_refl _ contains).
        assumption.
      * apply contains_app_l.
        specialize (IHtrunk1 _ (compose bfirst f) tree1 eq_refl _ contains).
        assumption.
    - destruct head as [ entry | ].
      * apply lctail.
        apply contains_app_r.
        specialize (IHtrunk2 _ (compose bsecond f) tree2 eq_refl _ contains).
        assumption.
      * apply contains_app_r.
        specialize (IHtrunk2 _ (compose bsecond f) tree2 eq_refl _ contains).
        assumption.
Qed.
Lemma bentries_contains {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} {tree: BTree K V P}: forall path: BPath, forall contains: BContainsPath tree path, ListContains (existT _ path (bget_contained tree path contains)) (bentries tree).
Proof.
  apply bentries_contains'.
Qed.
Lemma bcontains_entries' {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} {f: BPath -> BPath} {tree: BTree K V (compose f P)}: forall entry: { path: BPath & BEntry K V (P path) }, ListContains entry (bentries' f tree) -> existsTS path: BPath, existsSS e: eqS (projT1 entry) (f path), BTreeContains tree path (convert e (fun path => BEntry K V (P path)) (projT2 entry)).
Proof.
  remember (btree_trunk tree) as trunk.
  revert P f tree Heqtrunk.
  induction trunk as [ | root trunk1 IHtrunk1 trunk2 IHtrunk2 ]; intros P f tree etrunk entry contains; destruct tree as [ | head tree1 tree2 ]; inversion_hset etrunk; simpl in contains.
  + inversion contains.
  + destruct head as [ entry' | ].
    - inversion_hset contains; simpl.
      * exists bend.
        exists (eqS_refl _).
        rewrite convert_id.
        exists trueS.
        reflexivity.
      * rename H0 into contains.
        apply app_contains in contains.
        destruct contains as [ contains | contains ].
        ** apply IHtrunk1 in contains; try reflexivity.
           destruct contains as [ path [ e contains ] ].
           exists (bfirst path).
           exists e.
           assumption.
        ** apply IHtrunk2 in contains; try reflexivity.
           destruct contains as [ path [ e contains ] ].
           exists (bsecond path).
           exists e.
           assumption.
    - apply app_contains in contains.
      destruct contains as [ contains | contains ].
      * apply IHtrunk1 in contains; try reflexivity.
        destruct contains as [ path [ e contains ] ].
        exists (bfirst path).
        exists e.
        assumption.
      * apply IHtrunk2 in contains; try reflexivity.
        destruct contains as [ path [ e contains ] ].
        exists (bsecond path).
        exists e.
        assumption.
Qed.
Lemma bcontains_entries {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} {tree: BTree K V P}: forall entry: { path: BPath & BEntry K V (P path) }, ListContains entry (bentries tree) -> BTreeContains tree (projT1 entry) (projT2 entry).
Proof.
  intros entry contains.
  apply bcontains_entries' in contains.
  destruct contains as [ path [ e contains ] ].
  destruct e.
  rewrite convert_id in contains.
  assumption.
Qed.

Definition BTreeForallS {K: Type} {V: K -> Type} (R: forall key: K, V key -> SProp): forall {P: BPath -> K -> SProp}, BTree K V P -> SProp
:= fix BTreeForallS {P: BPath -> K -> SProp} (tree: BTree K V P): SProp
:= match tree with
   | bempty => TrueS
   | bnode head ltree rtree => AndS (OptionS (fun entry => R entry.(bekey) entry.(bevalue)) head)
                                    (AndS (BTreeForallS ltree) (BTreeForallS rtree))
   end.

Lemma btforallS_forall {K: Type} {V: K -> Type} {R: forall key: K, V key -> SProp}: forall {P: BPath -> K -> SProp}, forall {tree: BTree K V P}, BTreeForallS R tree -> forall path: BPath, forall entry: BEntry K V (P path), BTreeContains tree path entry -> R entry.(bekey) entry.(bevalue).
Proof.
  intros P tree.
  induction tree; unfold BTreeContains; simpl; intros fa path entry contains.
  + destruct contains as [ [ ] _ ].
  + destruct fa as [ fahead [ fa1 fa2 ] ].
    destruct contains as [ contains e ].
    destruct e.
    destruct path as [ | path | path ].
    - destruct head as [ entry | ]; destruct contains.
      assumption.
    - apply IHtree1; try assumption.
      apply btreecontains_get_contained.
    - apply IHtree2; try assumption.
      apply btreecontains_get_contained.
Qed.

Lemma forall_btforallS {K: Type} {V: K -> Type} (R: forall key: K, V key -> SProp): forall {P: BPath -> K -> SProp}, forall tree: BTree K V P, (forall path: BPath, forall entry: BEntry K V (P path), BTreeContains tree path entry -> R entry.(bekey) entry.(bevalue)) -> BTreeForallS R tree.
Proof.
  intros P tree.
  induction tree; unfold BTreeContains; simpl; intro fa.
  + constructor.
  + repeat split.
    - specialize (fa bend).
      destruct head as [ entry | ]; simpl.
      * apply fa.
        exists trueS.
        reflexivity.
      * constructor.
    - specialize (fun path => fa (bfirst path)).
      apply IHtree1.
      intros path entry contains.
      apply fa.
      assumption.
    - specialize (fun path => fa (bsecond path)).
      apply IHtree2.
      intros path entry contains.
      apply fa.
      assumption.
Qed.

Lemma btforallS_mono {K: Type} {V: K -> Type} (R R': forall key: K, V key -> SProp) {P: BPath -> K -> SProp} (tree: BTree K V P): (forall key: K, forall v: V key, R key v -> R' key v) -> BTreeForallS R tree -> BTreeForallS R' tree.
Proof.
  intros mono fa.
  apply forall_btforallS.
  intros path entry contains.
  apply mono.
  apply (btforallS_forall fa).
  assumption.
Qed.

Lemma btforallS_get_contained {K: Type} {V: K -> Type} (R: forall key: K, V key -> SProp) {P: BPath -> K -> SProp} (tree: BTree K V P) (fa: BTreeForallS R tree) (path: BPath) (contains: BContainsPath tree path): R (bget_contained tree path contains).(bekey) (bget_contained tree path contains).(bevalue).
Proof.
  apply (btforallS_forall fa).
  apply btreecontains_get_contained.
Qed.

Lemma btforallS_singleton {K: Type} {V: K -> Type} (R: forall key: K, V key -> SProp) {P: BPath -> K -> SProp} (path: BPath) (entry: BEntry K V (P path)): R entry.(bekey) entry.(bevalue) -> BTreeForallS R (bsingleton path entry).
Proof.
  intro r.
  apply forall_btforallS.
  intros path' entry' [ contains e ].
  destruct e.
  rewrite bget_contains_singleton.
  destruct (bcontains_singleton contains).
  rewrite convert_id.
  assumption.
Qed.

Lemma btforallS_extend {K: Type} {V: K -> Type} (R: forall key: K, V key -> SProp) {P: BPath -> K -> SProp} (tree: BTree K V P) (fa: BTreeForallS R tree) (path: BPath) (entry: BEntry K V (P path)) (rentry: R entry.(bekey) entry.(bevalue)) (tree': BTree K V P): BExtends tree path entry tree' -> BTreeForallS R tree'.
Proof.
  intro extends.
  apply forall_btforallS.
  intros path' entry' contains'.
  destruct contains' as [ contains' e' ].
  destruct e'.
  destruct (decidableS (eqS path path')) as [ e | ne ].
  + destruct e.
    rewrite (bget_contained_extends_eq extends).
    assumption.
  + rewrite (bget_contained_extends_neq extends ne).
    apply (btforallS_forall fa).
    apply btreecontains_get_contained.
Qed.

Lemma btree_splitterS {K: Type} {V: K -> Type} {P: BPath -> K -> SProp} (tree: BTree K V P) (Pl Pr: forall path: BPath, BContainsPath tree path -> SProp): (forall path: BPath, forall contains: BContainsPath tree path, SumBoolS (Pl path contains) (Pr path contains)) -> SumBoolS (existsTS path: BPath, existsSS contains: BContainsPath tree path, Pl path contains) (forall path: BPath, forall contains: BContainsPath tree path, Pr path contains).
Proof.
  intro split.
  induction tree; simpl in *.
  + right.
    intros path [ ].
  + specialize (IHtree1 (fun path => Pl (bfirst path)) (fun path => Pr (bfirst path)) (fun path => split (bfirst path))).
    destruct IHtree1 as [ IHtree1 | IHtree1 ]; [ left; destruct IHtree1 as [ path [ contains IHtree1 ] ]; exists (bfirst path); exists contains; assumption | ].
    specialize (IHtree2 (fun path => Pl (bsecond path)) (fun path => Pr (bsecond path)) (fun path => split (bsecond path))).
    destruct IHtree2 as [ IHtree2 | IHtree2 ]; [ left; destruct IHtree2 as [ path [ contains IHtrunk2 ] ]; exists (bsecond path); exists contains; assumption | ].
    destruct head; simpl in *.
    - specialize (split bend trueS).
      destruct split as [ p | p' ]; [ left; exists bend; exists trueS; assumption | ].
      right.
      intros path contains.
      destruct path as [ | path | path ].
      * apply p'.
      * apply IHtree1.
      * apply IHtree2.
    - right.
      intros path contains.
      destruct path as [ | path | path ].
      * destruct contains.
      * apply IHtree1.
      * apply IHtree2.
Qed.



(* A Sub-Countable Map, i.e. SCMap, is a binary tree implementing a partial map from a subcountable set. *)
Definition SCMap (K: Type) `{SubCountable K} (V: K -> Type): Type
:= BTree K V (fun path k => eqS (scpath k) path).

Definition SCMapContains {K: Type} `{SubCountable K} {V: K -> Type} (map: SCMap K V) (k: K): SProp
:= BContainsPath map (scpath k).

#[local] Instance SCMapContains_DecidableS {K: Type} {K_SubCountable: SubCountable K} {V: K -> Type} (map: SCMap K V) (k: K): DecidableS (SCMapContains map k).
Proof.
  unfold SCMapContains.
  apply _.
Qed.
#[local] Instance SCMapContains_FiniteS {K: Type} {K_SubCountable: SubCountable K} {V: K -> Type} (map: SCMap K V): FiniteS (SCMapContains map).
Proof.
simple refine (bij_FiniteS (fun k _ => scpath k) (fun path contains => (bget_contained map path contains).(bekey)) _ _ _ _); simpl.
+ trivial.
+ intros path contains.
  unfold SCMapContains.
  pose proof (bget_contained map path contains).(bekeyP) as e.
  simpl in e.
  symmetry in e.
  destruct e.
  assumption.
+ intros.
  apply scpath_inj.
  assumption.
+ intros path contains.
  apply (bget_contained map path contains).(bekeyP).
Qed.

Definition scentry_value {K: Type} {K_SubCountable: SubCountable K} {V: K -> Type} {k: K} (entry: BEntry K V (fun k' => eqS (scpath k') (scpath k))): V k
:= convert (scpath_injS entry.(bekeyP)) V entry.(bevalue).
Lemma scmap_contains_key {K: Type} {K_SubCountable: SubCountable K} {V: K -> Type} (map: SCMap K V) (k: K) (contains: SCMapContains map k): eqS (bget_contained map (scpath k) contains).(bekey) k.
Proof.
  apply eq_eqS.
  apply scpath_inj.
  apply eqS_eq.
  exact (bget_contained map (scpath k) contains).(bekeyP).
Qed.

Definition scmget_contained {K: Type} `{SubCountable K} {V: K -> Type} (map: SCMap K V) (k: K) (contains: SCMapContains map k): V k
:= scentry_value (bget_contained map (scpath k) contains).

Lemma scmap_contains {K: Type} {K_SubCountable: SubCountable K} {V: K -> Type} {map: SCMap K V} {path: BPath} (contains: BContainsPath map path): SCMapContains map (bget_contained map path contains).(bekey).
Proof.
  unfold SCMapContains.
  generalize (bget_contained map path contains).(bekeyP).
  generalize (bget_contained map path contains).(bekey).
  intros ? e.
  destruct e.
  assumption.
Qed.

Definition scmget {K: Type} `{SubCountable K} {V: K -> Type} (map: SCMap K V) (k: K): option (V k)
:= option_map scentry_value (bget map (scpath k)).

Definition scmempty {K: Type} `{SubCountable K} {V: K -> Type}: SCMap K V
:= bempty.

(* SCMExtends is a non-strict property because it is often used for termination, and Rocq can only structurally recurse on non-strict propositions.
 * It indicates that the latter map is the former map extended with the given value added at or replacing the value for the given key.
 *)
Definition SCMExtends {K: Type} `{SubCountable K} {V: K -> Type} (map: SCMap K V) (k: K) (v: V k) (map': SCMap K V): Prop
:= BExtends map (scpath k) {| bekey := k; bevalue := v; bekeyP := eqS_refl _ |} map'.

Lemma scmextends_contains_key {K: Type} {K_SubCountable: SubCountable K} {V: K -> Type} {map: SCMap K V} {k: K} {v: V k} {map': SCMap K V}: SCMExtends map k v map' -> SCMapContains map' k.
Proof.
  apply bextends_contains_path.
Qed.
Lemma scmextends_contains {K: Type} {K_SubCountable: SubCountable K} {V: K -> Type} {map: SCMap K V} {k: K} {v: V k} {map': SCMap K V}: SCMExtends map k v map' -> forall {k': K}, SCMapContains map k' -> SCMapContains map' k'.
Proof.
  intros extends k' contains.
  apply bextends_contains with (scpath k') in extends; assumption.
Qed.
Lemma scmcontains_extends {K: Type} {K_SubCountable: SubCountable K} {V: K -> Type} {map: SCMap K V} {k: K} {v: V k} {map': SCMap K V}: SCMExtends map k v map' -> forall {k': K}, SCMapContains map' k' -> OrS (eqS k k') (SCMapContains map k').
Proof.
  intros extends k' contains'.
  destruct (bcontains_extends extends contains') as [ e | contains ].
  + left.
    apply scpath_injS.
    assumption.
  + right.
    assumption.
Qed.
Lemma scmcontains_extends_neq {K: Type} {K_SubCountable: SubCountable K} {V: K -> Type} {map: SCMap K V} {k: K} {v: V k} {map': SCMap K V}: SCMExtends map k v map' -> forall {k': K}, SCMapContains map' k' -> (eqS k k' -> FalseS) -> SCMapContains map k'.
Proof.
  intros extends k' contains' ne.
  destruct (scmcontains_extends extends contains') as [ e | contains ]; try assumption.
  destruct (ne e).
Qed.

Lemma scmget_contained_extends_eq {K: Type} {K_SubCountable: SubCountable K} {V: K -> Type} {map: SCMap K V} {k: K} {v: V k} {map': SCMap K V} (extends: SCMExtends map k v map') (contains': SCMapContains map' k): scmget_contained map' k contains' = v.
Proof.
  unfold scmget_contained.
  rewrite (bget_contained_extends_eq extends).
  unfold scentry_value.
  rewrite convert_id.
  reflexivity.
Qed.
Lemma scmget_contained_extends_neq {K: Type} {K_SubCountable: SubCountable K} {V: K -> Type} {map: SCMap K V} {k: K} {v: V k} {map': SCMap K V} (extends: SCMExtends map k v map') {k': K} (ne: eqS k k' -> FalseS) (contains': SCMapContains map' k'): scmget_contained map' k' contains' = scmget_contained map k' (scmcontains_extends_neq extends contains' ne).
Proof.
  unfold scmget_contained.
  erewrite (bget_contained_extends_neq extends (fun e => ne (scpath_injS e))).
  reflexivity.
Qed.

(* Note that we can show that extension of partial maps is co-well-founded knowing only that the domain is subfinite. *)
Lemma sfmap_cwf {K: Type} {K_SubFinite: SubFinite K} {V: K -> Type} (R: forall k: K, V k -> V k -> Prop) (map: SCMap K V): (forall k: K, forall v: V k, CoAcc (R k) v) -> CoAcc (fun map map' => exists k: K, exists2 v': V k, SCMExtends map k v' map' & forall contains: SCMapContains map k, R k (scmget_contained map k contains) v') map.
Proof.
  intros v_cwf.
  assert (forall path, forall entry: BEntry K V (fun k => eqS (scpath k) path), CoAcc (fun entry entry' => R entry.(bekey) entry.(bevalue) (convert (scpath_injS (eqS_trans entry'.(bekeyP) (eqS_sym entry.(bekeyP)))) V entry'.(bevalue))) entry) as entry_cwf.
  + intros path entry.
    generalize (eq_refl entry.(bevalue)).
    generalize entry.(bevalue) at 2.
    replace entry.(bevalue) with (convert (eqS_refl entry.(bekey)) V entry.(bevalue)); [ | rewrite convert_id; reflexivity ].
    generalize (eqS_refl entry.(bekey)).
    generalize entry.(bekey) at 2 3 4 6.
    intros k ek v.
    specialize (v_cwf k v).
    revert entry ek.
    induction v_cwf as [ v _ IHv ].
    intros entry ek ev.
    destruct (eqS_eq ek); rewrite convert_id in ev; clear ek.
    destruct ev.
    constructor.
    intros entry' r.
    eapply IHv; eauto.
  + induction (bextends_cwf (P := fun path k => eqS (scpath k) path) (sftrunk K) (fun _ _ => True) (fun path entry entry' => R entry.(bekey) entry.(bevalue) (convert (scpath_injS (eqS_trans entry'.(bekeyP) (eqS_sym entry.(bekeyP)))) V entry'.(bevalue))) map) as [ map _ IHmap ]; try auto.
    constructor.
    intros map' [ k [ v extends r ] ].
    apply IHmap; clear IHmap.
    exists (scpath k); try apply sfcontains.
    exists {| bekey := k; bevalue := v; bekeyP := eqS_refl (scpath k) |}; try assumption.
    unfold scmget in r.
    pose proof (bget_contains map (scpath k)) as contains.
    destruct (bget map (scpath k)) as [ entry | ]; [ | trivial ].
    simpl in *.
    destruct contains as [ contains e ].
    destruct e.
    specialize (r contains).
    unfold scmget_contained in r.
    unfold scentry_value in r.
    destruct (bget_contained map (scpath k) contains) as [ k' e v' ]; cbn in *.
    destruct (eqS_eq (scpath_injS e)).
    rewrite convert_id in r.
    rewrite convert_id.
    assumption.
Qed.

(* scmupdate is the key function for conceptually mutating a subcountable map.
 * One provides it with a map, a key, and an update to be applied to the existing value (if any) of the map.
 * The update itself takes the optional existing value,
 * and then it returns either the value to replace it with (or add, if none were present), or an indication to make no change, or an indication that the update is incompatible with the preexisting value.
 * scmupdate then either returns the corresponding updated map, or an indication that no change was made to the map, or an indication that the update is incompatible with the map.
 *)
Definition scmupdate {K: Type} `{SubCountable K} {V: K -> Type} (map: SCMap K V) (k: K) (update: DeciderS (SCMapContains map k) -> option (option (V k))): option (option (SCMap K V))
:= bupdate map (scpath k) (fun entry => option_map (option_map (fun v => {| bekey := k; bevalue := v; bekeyP := eqS_refl (scpath k) |})) (update entry)).

Lemma scmupdate_extends
      {K: Type}
      {K_SubCountable: SubCountable K}
      {V: K -> Type}
      (map: SCMap K V)
      (k: K)
      (update: DeciderS (SCMapContains map k) -> option (option (V k)))
      (D: V k -> Prop)
      (E: SCMapContains map k -> Prop)
      (I: SCMapContains map k -> Prop)
      (R: SCMapContains map k -> V k -> Prop)
    : (forall ncontains: SCMapContains map k -> FalseS, match update (sbrightS ncontains) with None => False | Some None => False | Some (Some v) => D v end)
   -> (forall contains: SCMapContains map k, match update (sbleftS contains) with None => E contains | Some None => I contains | Some (Some v') => R contains v' end)
   -> match scmupdate map k update with
      | None => existsSP contains: SCMapContains map k,
                E contains
      | Some None => existsSP contains: SCMapContains map k,
                     I contains
      | Some (Some map') => exists2 v': V k,
                            SCMExtends map k v' map'
                          & ((SCMapContains map k -> FalseS) -> D v')
                         /\ (forall contains: SCMapContains map k, R contains v')
      end.
Proof.
  intros update_none update_some.
  unfold scmupdate.
  pose proof (bupdate_extends map
                              (scpath k)
                              (fun entry => option_map (option_map (fun v => {| bekey := k; bevalue := v; bekeyP := eqS_refl (scpath k) |})) (update entry))
                              (fun entry => D (scentry_value entry))
                              E
                              I
                              (fun contains entry' => R contains (scentry_value entry'))) as extends.
  simpl in extends.
  fold (SCMapContains map k) in *.
  match goal with extends: ?P -> ?P' -> _ |- _ => assert P as p; [ | assert P' as p'; [ | specialize (extends p p'); clear p p' ] ] end.
  + intro ncontains.
    specialize (update_none ncontains).
    destruct (update (sbrightS ncontains)) as [ [ v | ] | ]; try assumption; simpl.
    unfold scentry_value.
    cbn.
    rewrite convert_id.
    assumption.
  + intro contains.
    specialize (update_some contains).
    destruct (update (sbleftS contains)) as [ [ v' | ] | ]; try assumption; simpl.
    unfold scentry_value.
    cbn.
    rewrite convert_id.
    assumption.
  + unfold DeciderS in *.
    unfold SCMapContains in *.
    destruct (bupdate map (scpath k) (fun entry => option_map (option_map (fun v => {| bekey := k; bevalue := v; bekeyP := eqS_refl (scpath k) |})) (update entry))) as [ [ map' | ] | ]; try assumption.
    destruct extends as [ entry' extends r ].
    exists (scentry_value entry').
    - unfold SCMExtends.
      unfold scentry_value.
      destruct entry' as [ k' e v' ].
      cbn.
      destruct (eqS_eq (scpath_injS e)).
      rewrite convert_id.
      assumption.
    - unfold scmget.
      assumption.
Qed.

(* scmpath and scmtrunk are used when the potential values of an SCMap have a common indexing structure *)
Definition scmpath {K: Type} `{SubCountable K} (k: K) (vpath: BPath): BPath
:= bpath_pair (scpath k) vpath.
Definition scmtrunk {K: Type} `{SubCountable K} {V: K -> Type} (map: SCMap K V) (vtrunk: forall k: K, V k -> BTrunk): BTrunk
:= btrunk_pair (btree_trunk map) (fun path contains => vtrunk (bget_contained map path (btree_trunk_contains' contains)).(bekey) (bget_contained map path (btree_trunk_contains' contains)).(bevalue)).
Lemma scmpath_inj {K: Type} {K_SubCountable: SubCountable K} (k: K) (vpath: BPath) (k': K) (vpath': BPath): scmpath k vpath = scmpath k' vpath' -> k = k' /\ vpath = vpath'.
Proof.
  unfold scmpath.
  intro e.
  apply bpath_pair_inj in e.
  destruct e as [ ek ev ].
  apply scpath_inj in ek.
  split; assumption.
Qed.
Lemma scmtrunk_contains {K: Type} {K_SubCountable: SubCountable K} {V: K -> Type} (map: SCMap K V) (vtrunk: forall k: K, V k -> BTrunk): forall k: K, forall contains: SCMapContains map k, forall vpath: BPath, BTContains (vtrunk k (scmget_contained map k contains)) vpath -> BTContains (scmtrunk map vtrunk) (scmpath k vpath).
Proof.
  intros k kcontains vpath vcontains.
  unfold scmget_contained in vcontains.
  unfold scentry_value in vcontains.
  eapply btcontains_pair with (btree_trunk_contains kcontains).
  merge kcontains (btree_trunk_contains' (btree_trunk_contains kcontains)).
  destruct (scpath_injS (bget_contained map (scpath k) kcontains).(bekeyP)).
  rewrite convert_id in vcontains.
  eassumption.
Qed.



(* A Sub-Countable Set, i.e. SCSet, is a binary tree implementing a finite subset of a subcountable map. *)
Definition SCSet (A: Type) `{SubCountable A}: Type
:= SCMap A (fun _ => unit).
Definition SCSetContains {A: Type} `{SubCountable A}: SCSet A -> A -> SProp
:= SCMapContains.
#[local] Instance SCSetContains_DecidableS {T: Type} {T_SubCountable: SubCountable T} (set: SCSet T) (t: T): DecidableS (SCSetContains set t).
Proof.
  unfold SCSetContains.
  apply _.
Qed.
#[local] Instance SCSetContains_FiniteS {T: Type} {T_SubCountable: SubCountable T} (set: SCSet T): FiniteS (SCSetContains set).
Proof.
  unfold SCSetContains.
  apply _.
Qed.

Lemma scset_contains {A: Type} {A_SubCountable: SubCountable A} {set: SCSet A} {path: BPath} (contains: BContainsPath set path): SCSetContains set (bget_contained set path contains).(bekey).
Proof.
  apply scmap_contains.
Qed.

Lemma scset_contains_key {A: Type} {A_SubCountable: SubCountable A} (set: SCSet A) (a: A) (contains: SCSetContains set a): (bget_contained set (scpath a) contains).(bekey) = a.
Proof.
  apply eqS_eq.
  apply scmap_contains_key.
Qed.

Lemma scset_splitterS {T: Type} {T_SubCountable: SubCountable T} (set: SCSet T) (Pl Pr: forall t: T, SCSetContains set t -> SProp): (forall t: T, forall contains: SCSetContains set t, SumBoolS (Pl t contains) (Pr t contains)) -> SumBoolS (existsTS t: T, existsSS contains: SCSetContains set t, Pl t contains) (forall t: T, forall contains: SCSetContains set t, Pr t contains).
Proof.
  intro split.
  destruct (btree_splitterS set (fun path contains => Pl (bget_contained set path contains).(bekey) (scset_contains contains)) (fun path contains => Pr (bget_contained set path contains).(bekey) (scset_contains contains))) as [ pl | pr ].
  + intros path contains.
    apply split.
  + left.
    destruct pl as [ path [ contains pl ] ].
    eexists.
    eexists.
    eassumption.
  + right.
    intros t contains.
    specialize (pr (scpath t) contains).
    revert pr.
    generalize (scset_contains contains).
    rewrite scset_contains_key.
    trivial.
Qed.
Lemma scset_splitterS' {T: Type} {T_SubCountable: SubCountable T} (set: SCSet T) (Pl Pr: forall t: T, SCSetContains set t -> SProp): (forall t: T, forall contains: SCSetContains set t, SumBoolS (Pl t contains) (Pr t contains)) -> SumBoolS (forall t: T, forall contains: SCSetContains set t, Pl t contains) (existsTS t: T, existsSS contains: SCSetContains set t, Pr t contains).
Proof.
  intro split.
  destruct (scset_splitterS set Pr Pl); try (constructor; assumption).
  intros t contains.
  specialize (split t contains).
  destruct split; constructor; assumption.
Qed.



(* An indexed map, i.e. IMap, is a binary tree whose keys are at indexes given by an explicit function.
 * Unlike SCMaps, this indexing function is not expected to be injective.
 * However, the expectation is that there are subsets from which it is injective, and that an indexed map will only be used with keys from such a subset.
 * The particular subset at hand, though, will expand over time depending on how the algorithm advances, e.g. due to label-listeners firing.
 * When such an expansion occurs, the IMaps used by the algorithm stays the same, but the IMForallS invariants maintained by the algorithm are relaxes to allow more keys to be added to the map.
 *)
Definition IMap {K: Type} (index: K -> BPath) (V: Type): Type
:= BTree K (fun _ => V) (fun path key => eqS (index key) path).
Definition IMForallS {K: Type} {index: K -> BPath} (KV: K -> SProp) {V: Type} (R: K -> V -> SProp): IMap index V -> SProp
:= BTreeForallS (fun k v => AndS (KV k) (R k v)).
Definition IMContains {K: Type} {index: K -> BPath} {V: Type} (map: IMap index V) (key: K): SProp
:= BContainsPath map (index key).
Definition imget_contained {K: Type} {index: K -> BPath} {V: Type} (map: IMap index V) (key: K) (contains: IMContains map key): V
:= (bget_contained map (index key) contains).(bevalue).
Definition imget {K: Type} {index: K -> BPath} {V: Type} (map: IMap index V) (key: K): option V
:= option_map (bevalue (V := fun _ => V)) (bget map (index key)).
(* IMExtends is a non-strict property because it is often used for termination, and Rocq can only structurally recurse on non-strict propositions.
 * It indicates that the latter map is the former map extended with the given key-value pair added at or replacing the key-value pair at the index of the given key.
 *)
Definition IMExtends {K: Type} {index: K -> BPath} {V: Type} (map: IMap index V) (key: K) (value: V) (map': IMap index V): Prop
:= BExtends map (index key) {| bekey := key; bekeyP := eqS_refl _; bevalue := value |} map'.
Definition imempty {K: Type} (index: K -> BPath) (V: Type): IMap index V
:= bempty.
Definition imsingleton {K: Type} (index: K -> BPath) {V: Type} (k: K) (v: V): IMap index V
:= bsingleton (index k) {| bekey := k; bekeyP := eqS_refl (index k); bevalue := v |}.
(* imupdate is the key function for conceptually mutating an indexed map.
 * One provides it with a map, a key, and an update to be applied to the existing value (if any) of the map.
 * The update itself takes the optional existing value,
 * and then it returns either the value to replace it with (or add, if none were present) or an indication to make no change.
 * imupdate then either returns the corresponding updated map or an indication that no change was made to the map.
 *)
Definition imupdate {K: Type} {index: K -> BPath} {V: Type} (map: IMap index V) (k: K) (update: option V -> option V): option (IMap index V)
:= match bupdate map (index k) (fun entry => Some (option_map (fun v => {| bekey := k; bevalue := v; bekeyP := eqS_refl _ |}) (match entry with
                                                                                                                               | sbleftS contains => update (Some (bget_contained map (index k) contains).(bevalue))
                                                                                                                               | sbrightS _ => update None
                                                                                                                               end))) with
   | None => None
   | Some map => map
   end.
Definition imentries {K: Type} {index: K -> BPath} {V: Type} (map: IMap index V): list (prod K V)
:= List.map (fun entry: sigT (fun path => BEntry K (fun _ => V) (fun key => eqS (index key) path)) => pair (projT2 entry).(bekey) (projT2 entry).(bevalue) : prod K V) (bentries map).

Lemma imget_contains {K: Type} {index: K -> BPath} {V: Type} (map: IMap index V) (k: K): match imget map k with None => IMContains map k -> False | Some v => existsSP contains: IMContains map k, imget_contained map k contains = v end.
Proof.
  unfold imget.
  pose proof (bget_contains map (index k)) as contains.
  destruct (bget map (index k)) as [ entry | ]; simpl.
  + destruct contains as [ contains e ].
    exists contains.
    destruct e.
    reflexivity.
  + assumption.
Qed.
Lemma imget_contained_imget {K: Type} {index: K -> BPath} {V: Type} {map: IMap index V} {k: K} (contains: IMContains map k): imget map k = Some (imget_contained map k contains).
Proof.
  pose proof (imget_contains map k) as e.
  destruct (imget map k) as [ v | ].
  + destruct e as [ contains' e ].
    destruct e.
    reflexivity.
  + destruct (e contains).
Qed.

Lemma imempty_ncontains {K: Type} {index: K -> BPath} {V: Type} {k: K}: IMContains (imempty index V) k -> FalseS.
Proof.
  unfold IMContains.
  unfold imempty.
  trivial.
Qed.

Lemma imextends_contains {K: Type} {index: K -> BPath} {V: Type} {map: IMap index V} {k: K} {v: V} {map': IMap index V}: IMExtends map k v map' -> forall {k': K}, IMContains map k' -> IMContains map' k'.
Proof.
  unfold IMExtends.
  unfold IMContains.
  intros extends k'.
  apply (bextends_contains extends).
Qed.
Lemma imextends_contains_key {K: Type} {index: K -> BPath} {V: Type} {map: IMap index V} {k: K} {v: V} {map': IMap index V}: IMExtends map k v map' -> IMContains map' k.
Proof.
  apply bextends_contains_path.
Qed.
Lemma imcontains_extends {K: Type} {index: K -> BPath} {V: Type} {map: IMap index V} {k: K} {v: V} {map': IMap index V}: IMExtends map k v map' -> forall {k': K}, IMContains map' k' -> OrS (eqS (index k) (index k')) (IMContains map k').
Proof.
  intros extends k'.
  apply (bcontains_extends extends).
Qed.
Lemma imcontains_extends_neq {K: Type} {index: K -> BPath} {V: Type} {map: IMap index V} {k: K} {v: V} {map': IMap index V}: IMExtends map k v map' -> forall {k': K}, IMContains map' k' -> (eqS (index k) (index k') -> FalseS) -> IMContains map k'.
Proof.
  intros extends k'.
  apply (bcontains_extends_neq extends).
Qed.
Lemma imget_contained_extends_eq {K: Type} {index: K -> BPath} {V: Type} {map: IMap index V} {k: K} {v: V} {map': IMap index V} (extends: IMExtends map k v map') (contains': IMContains map' k): imget_contained map' k contains' = v.
Proof.
  unfold imget_contained.
  rewrite (bget_contained_extends_eq extends).
  reflexivity.
Qed.
Lemma imget_contained_extends_neq {K: Type} {index: K -> BPath} {V: Type} {map: IMap index V} {k: K} {v: V} {map': IMap index V} (extends: IMExtends map k v map') {k': K} (ne: eqS (index k) (index k') -> FalseS) (contains': IMContains map' k'): imget_contained map' k' contains' = imget_contained map k' (imcontains_extends_neq extends contains' ne).
Proof.
  unfold imget_contained.
  rewrite (bget_contained_extends_neq extends ne).
  reflexivity.
Qed.

Lemma imupdate_extends
      {K: Type}
      {index: K -> BPath}
      {V: Type}
      (map: IMap index V)
      (k: K)
      (update: option V -> option V)
      (I: V -> Prop)
      (D: V -> Prop)
      (R: V -> V -> Prop)
    : (match update None with None => False | Some v => D v end)
   -> (forall v: V, match update (Some v) with None => I v | Some v' => R v v' end)
   -> match imupdate map k update with
      | None => existsSP contains: IMContains map k,
                I (imget_contained map k contains)
      | Some map' => exists2 v': V,
                     IMExtends map k v' map'
                   & match imget map k with
                     | None => D v'
                     | Some v => R v v'
                     end
      end.
Proof.
  intros d r.
  unfold imupdate.
  pose proof (bupdate_extends map (index k) (fun entry => Some (option_map (fun v => {| bekey := k; bekeyP := eqS_refl (index k); bevalue := v |}) (match entry with sbleftS contains => update (Some (bget_contained map (index k) contains).(bevalue)) | sbrightS _ => update None end))) (fun entry => entry.(bekey) = k /\ D entry.(bevalue)) (fun _ => False) (fun contains => I (bget_contained map (index k) contains).(bevalue)) (fun contains entry' => entry'.(bekey) = k /\ R (bget_contained map (index k) contains).(bevalue) entry'.(bevalue))) as extends.
  simpl in extends.
  match goal with extends: ?P -> _ |- _ => assert P as p by (intro ncontains; destruct (update None); try split; trivial); specialize (extends p); clear p end; clear d.
  match goal with extends: ?P -> _ |- _ => assert P as p by (intro contains; specialize (r (bget_contained map (index k) contains).(bevalue)); revert r; generalize (update (Some (bget_contained map (index k) contains).(bevalue))); intros [ ? | ]; try split; trivial); specialize (extends p); clear p end; clear r.
  destruct (bupdate map (index k)) as [ [ map' | ] | ].
  + destruct extends as [ entry' extends r ].
    destruct entry' as [ k' e v ].
    cbn in r.
    destruct r as [ d r ].
    exists v.
    - unfold IMExtends.
      destruct (decidableS (BContainsPath map (index k))) as [ contains | ncontains ].
      * specialize (r contains).
        destruct r as [ ek _ ].
        destruct ek.
        assumption.
      * specialize (d ncontains).
        destruct d as [ ek _ ].
        destruct ek.
        assumption.
    - unfold imget.
      pose proof (bget_contains map (index k)) as contains.
      destruct (bget map (index k)) as [ entry | ]; simpl.
      * destruct contains as [ contains eentry ].
        destruct eentry.
        apply r.
      * apply d.
        intro contains'.
        exfalso.
        apply contains.
        assumption.
  + assumption.
  + destruct extends as [ _ [ ] ].
Qed.

Lemma imforallS_forall {K: Type} {index: K -> BPath} {KV: K -> SProp} {V: Type} {P: K -> V -> SProp}: (forall k k': K, KV k -> KV k' -> eqS (index k) (index k') -> k = k') -> forall {map: IMap index V}, IMForallS KV P map -> forall k: K, KV k -> forall contains: IMContains map k, P k (imget_contained map k contains).
Proof.
  intros kv_inj map fa k kv contains.
  unfold imget_contained.
  pose proof (btreecontains_get_contained _ _ contains) as p.
  apply (btforallS_forall fa) in p.
  destruct p as [ kv' p ].
  replace (bget_contained map (index k) contains).(bekey) with k in p; try assumption.
  apply kv_inj; try assumption.
  symmetry.
  apply (bget_contained map (index k) contains).(bekeyP).
Qed.

Lemma imforallS_mono' {K: Type} {index: K -> BPath} (KV KV': K -> SProp) {V: Type} (P P': K -> V -> SProp) (map: IMap index V): (forall k: K, KV k -> KV' k) -> (forall key: K, forall v: V, KV key -> P key v -> P' key v) -> IMForallS KV P map -> IMForallS KV' P' map.
Proof.
  intros kk' pp'.
  apply btforallS_mono.
  intros k v [ kv p ].
  split; auto.
Qed.

Lemma imforallS_singleton {K: Type} {index: K -> BPath} (KV: K -> SProp) {V: Type} (P: K -> V -> SProp) (k: K) (v: V): KV k -> P k v -> IMForallS KV P (imsingleton index k v).
Proof.
  intros kv p.
  apply (btforallS_singleton _ (index k) {| bekey := k; bekeyP := eqS_refl _; bevalue := v |}).
  split; assumption.
Qed.

Lemma imforallS_extend {K: Type} {index: K -> BPath} (KV: K -> SProp) {V: Type} (P: K -> V -> SProp) (map: IMap index V) (fa: IMForallS KV P map) (k: K) (kv: KV k) (v: V) (p: P k v) (map': IMap index V): IMExtends map k v map' -> IMForallS KV P map'.
Proof.
  apply btforallS_extend; try assumption.
  split; assumption.
Qed.

Lemma imcontains_singleton {K: Type} {index: K -> BPath} {V: Type} {k: K} {v: V} {k': K} (contains': IMContains (imsingleton index k v) k'): eqS (index k) (index k').
Proof.
  apply bcontains_singleton in contains'.
  assumption.
Qed.
Lemma imsingleton_contains {K: Type} {index: K -> BPath} {V: Type} (k: K) (v: V): IMContains (imsingleton index k v) k.
Proof.
  apply bsingleton_contains.
Qed.

Lemma imentries_contains {K: Type} {index: K -> BPath} {KV: K -> SProp} {V: Type} {P: K -> V -> SProp}: (forall k k': K, KV k -> KV k' -> eqS (index k) (index k') -> k = k') -> forall {map: IMap index V}, IMForallS KV P map -> forall k: K, KV k -> forall contains: IMContains map k, ListContains (pair k (imget_contained map k contains)) (imentries map).
Proof.
  intros kv_inj map fa k kv contains.
  unfold imentries.
  set (entry := existT (fun path => BEntry K (fun _ => V) (fun k => eqS (index k) path)) (index k) {| bekey := k; bevalue := imget_contained map k contains; bekeyP := eqS_refl _ |}).
  change (pair k (imget_contained map k contains)) with (pair (projT2 entry).(bekey) (projT2 entry).(bevalue)).
  apply (contains_map (fun entry': {path & BEntry K (fun _ => V) (fun k => eqS (index k) path)} => pair (projT2 entry').(bekey) (projT2 entry').(bevalue))).
  replace entry with (existT (fun path => BEntry K (fun _ => V) (fun k => eqS (index k) path)) (index k) (bget_contained map (index k) contains)).
  + apply (bentries_contains (index k) contains).
  + unfold entry.
    clear entry.
    f_equal.
    unfold imget_contained.
    unfold IMForallS in fa.
    apply (fun fa => btforallS_forall fa _ (bget_contained map (index k) contains)) in fa; try apply btreecontains_get_contained.
    destruct fa as [ kv' _ ].
    destruct (bget_contained map (index k) contains) as [ k' e v ].
    destruct (kv_inj k' k kv' kv e).
    reflexivity.
Qed.
Lemma imcontains_entries {K: Type} {index: K -> BPath} {KV: K -> SProp} {V: Type} {P: K -> V -> SProp}: forall {map: IMap index V}, IMForallS KV P map -> forall entry: prod K V, ListContains entry (imentries map) -> AndS (KV (fst entry)) (existsSS contains: IMContains map (fst entry), eqS (imget_contained map (fst entry) contains) (snd entry)).
Proof.
  intros map fa entry contains.
  unfold imentries in contains.
  apply map_contains in contains.
  destruct contains as [ [ path entry' ] e contains ].
  destruct e.
  cbn in *.
  apply bcontains_entries in contains.
  simpl in contains.
  unfold IMForallS in fa.
  apply (fun fa => btforallS_forall fa _ _ contains) in fa.
  simpl in fa.
  destruct fa as [ kv' _ ].
  split; try assumption; clear kv'.
  unfold IMContains.
  unfold BTreeContains in contains.
  destruct contains as [ contains e ].
  destruct e.
  exists (convertS (eqS_sym (bget_contained map path contains).(bekeyP)) (BContainsPath map) contains).
  unfold imget_contained.
  generalize (convertS (eqS_sym (bget_contained map path contains).(bekeyP)) (BContainsPath map) contains).
  replace (index (bget_contained map path contains).(bekey)) with path; try reflexivity.
  symmetry.
  apply eqS_eq.
  exact (bget_contained map path contains).(bekeyP).
Qed.

Lemma imap_cwf (trunk: BTrunk) {K: Type} {index: K -> BPath} (KV: K -> SProp) {V: Type} (P: K -> V -> SProp) (R: V -> V -> Prop) (map: IMap index V): IMForallS KV P map -> (forall k: K, forall v: V, KV k -> P k v -> Box (BTContains trunk (index k)) /\ CoAcc R v) -> CoAcc (fun map map' => existsTSP k: K, KV k & exists2 v': V, Box (P k v') /\ IMExtends map k v' map' & forall contains: IMContains map k, R (imget_contained map k contains) v') map.
Proof.
  intros pset ptrunk.
  assert (forall path, forall entry: BEntry K (fun _ => V) (fun k => eqS (index k) path), KV entry.(bekey) -> P entry.(bekey) entry.(bevalue) -> CoAcc (fun entry entry' => Box (KV entry'.(bekey)) /\ Box (P entry'.(bekey) entry'.(bevalue)) /\ R entry.(bevalue) entry'.(bevalue)) entry) as entry_cwf.
  + intros path entry kv p.
    apply ptrunk in p; try assumption.
    clear kv.
    destruct p as [ _ v_cwf ].
    revert v_cwf.
    generalize (eq_refl entry.(bevalue)).
    generalize entry.(bevalue) at 2 3.
    intros v e v_cwf.
    revert entry e.
    induction v_cwf as [ v _ IHv ].
    intros entry e.
    destruct e.
    constructor.
    intros entry' [ kv [ p r ] ].
    apply IHv with entry'.(bevalue); trivial.
  + induction (bextends_cwf trunk (fun _ entry => Box (KV entry.(bekey)) /\ Box (P entry.(bekey) entry.(bevalue))) (fun _ entry entry' => Box (KV entry'.(bekey)) /\ Box (P entry'.(bekey) entry'.(bevalue)) /\ R entry.(bevalue) entry'.(bevalue)) map) as [ map _ IHmap ].
    - constructor.
      intros map' [ k kv [ v' [ [ p ] extends ] r ] ].
      apply IHmap.
      * exists (index k); try (apply ptrunk with v'; assumption).
        eexists; try apply extends.
        cbn.
        pose proof (bget_contains map (index k)) as contains.
        destruct (bget map (index k)) as [ v | ]; simpl in contains.
        ** split; try (constructor; assumption).
           destruct contains as [ contains e ].
           destruct e.
           repeat split; try assumption.
           apply r.
        ** repeat constructor; assumption.
      * eapply btforallS_extend in extends; try eassumption.
        split; assumption.
    - intros path entry [ [ kv ] [ pentry ] ].
      apply entry_cwf; assumption.
    - intros path contains.
      apply (fun fa => btforallS_get_contained _ _ fa _ contains) in pset.
      apply entry_cwf; apply pset.
Qed.



(* An indexed finite subset of keys, akin to an indexed map. *)
Definition ISet {K: Type} (index: K -> BPath): Type
:= IMap index unit.
Definition ISForallS {K: Type} {index: K -> BPath} (KV P: K -> SProp): ISet index -> SProp
:= IMForallS KV (fun k _ => P k).
Definition ISContains {K: Type} {index: K -> BPath}: ISet index -> K -> SProp
:= IMContains.
(* ISExtends is a non-strict property because it is often used for termination, and Rocq can only structurally recurse on non-strict propositions.
 * It indicates that the latter set is the former set extended with the given previously-absent element.
 *)
Definition ISExtends {K: Type} {index: K -> BPath} (set: ISet index) (key: K) (set': ISet index): Prop
:= (ISContains set key -> False) /\ IMExtends set key tt set'.
Definition issingleton {K: Type} (index: K -> BPath) (k: K): ISet index
:= imsingleton index k tt.
(* isadd is the key function for conceptually mutating an indexed set.
 * One provides it with a set and an element.
 * Then it either returns the corresponding updated set or an indication that the element was already present in the set.
 *)
Definition isadd {K: Type} {index: K -> BPath} (set: ISet index) (k: K): option (ISet index)
:= imupdate set k (fun entry => match entry with None => Some tt | Some _ => None end).
Definition isvalues {K: Type} {index: K -> BPath} (set: ISet index): list K
:= map fst (imentries set).

Lemma isextends_contains {K: Type} {index: K -> BPath} {set: ISet index} {k: K} {set': ISet index}: ISExtends set k set' -> forall {k': K}, ISContains set k' -> ISContains set' k'.
Proof.
  intros [ _ extends ] k'.
  apply (imextends_contains extends).
Qed.
Lemma isextends_contains_key {K: Type} {index: K -> BPath} {set: ISet index} {k: K} {set': ISet index}: ISExtends set k set' -> ISContains set' k.
Proof.
  intros [ _ extends ].
  apply (imextends_contains_key extends).
Qed.
Lemma iscontains_extends {K: Type} {index: K -> BPath} {set: ISet index} {k: K} {set': ISet index}: ISExtends set k set' -> forall {k': K}, ISContains set' k' -> OrS (eqS (index k) (index k')) (ISContains set k').
Proof.
  intros [ _ extends ] k'.
  apply (imcontains_extends extends).
Qed.

Lemma isvalues_contains {K: Type} {index: K -> BPath} {KV: K -> SProp} {P: K -> SProp}: (forall k k': K, KV k -> KV k' -> eqS (index k) (index k') -> k = k') -> forall {set: ISet index}, ISForallS KV P set -> forall k: K, KV k -> ISContains set k -> ListContains k (isvalues set).
Proof.
  intros kv_inj set fa k kv contains.
  unfold isvalues.
  change k with (fst (pair k (imget_contained set k contains))).
  apply contains_map.
  unfold ISContains in contains.
  apply (imentries_contains kv_inj fa).
  assumption.
Qed.
Lemma iscontains_values {K: Type} {index: K -> BPath} {KV: K -> SProp} {P: K -> SProp} {set: ISet index}: ISForallS KV P set -> forall k: K, ListContains k (isvalues set) -> AndS (KV k) (ISContains set k).
Proof.
  intros fa k contains.
  unfold isvalues in contains.
  apply map_contains in contains.
  destruct contains as [ [ k' [ ] ] e contains ].
  simpl in e.
  destruct e.
  apply (imcontains_entries fa) in contains.
  destruct contains as [ kv [ contains _ ] ].
  split; assumption.
Qed.

Lemma isadd_extends {K: Type} {index: K -> BPath} (set: ISet index) (k: K): match isadd set k with None => Box (ISContains set k) | Some set' => ISExtends set k set' end.
Proof.
  unfold isadd.
  pose proof (imupdate_extends set k (fun entry => match entry with None => Some tt | Some _ => None end) (fun _ => True) (fun _ => True) (fun _ _ => False)) as extends.
  simpl in extends.
  match goal with extends: ?P -> _ |- _ => assert P as p by trivial; specialize (extends p); clear p end.
  match goal with extends: ?P -> _ |- _ => assert P as p by trivial; specialize (extends p); clear p end.
  destruct (imupdate set k (fun entry => match entry with None => Some tt | Some _ => None end)).
  + unfold ISExtends.
    destruct extends as [ [ ] extends r ].
    split; try assumption.
    pose proof (imget_contains set k) as contains.
    destruct (imget set k); destruct r.
    assumption.
  + unfold ISContains.
    constructor.
    destruct extends as [ contains _ ].
    assumption.
Qed.

Lemma isforallS_forall {K: Type} {index: K -> BPath} {KV P: K -> SProp}: (forall k k': K, KV k -> KV k' -> eqS (index k) (index k') -> k = k') -> forall {set: ISet index}, ISForallS KV P set -> forall k: K, KV k -> ISContains set k -> P k.
Proof.
  intros kv_inj set fa k kv contains.
  apply (imforallS_forall kv_inj fa) in contains; assumption.
Qed.

Lemma isforallS_mono' {K: Type} {index: K -> BPath} {KV KV': K -> SProp} (P P': K -> SProp) (set: ISet index): (forall k: K, KV k -> KV' k) -> (forall key: K, KV key -> P key -> P' key) -> ISForallS KV P set -> ISForallS KV' P' set.
Proof.
  intros kk' pp'.
  apply imforallS_mono'; auto.
Qed.
Lemma isforallS_mono {K: Type} {index: K -> BPath} {KV: K -> SProp} (P P': K -> SProp) (set: ISet index): (forall key: K, KV key -> P key -> P' key) -> ISForallS KV P set -> ISForallS KV P' set.
Proof.
  apply isforallS_mono'.
  trivial.
Qed.

Lemma isforallS_singleton {K: Type} {index: K -> BPath} (KV P: K -> SProp) (k: K): KV k -> P k -> ISForallS KV P (issingleton index k).
Proof.
  intros kv p.
  apply imforallS_singleton; assumption.
Qed.

Lemma isforallS_extend {K: Type} {index: K -> BPath} (KV P: K -> SProp) (set: ISet index) (fa: ISForallS KV P set) (k: K) (kv: KV k) (p: P k) (set': ISet index): ISExtends set k set' -> ISForallS KV P set'.
Proof.
  intros [ _ extends ].
  eapply imforallS_extend; try eassumption.
Qed.

Lemma iscontains_singleton {K: Type} {index: K -> BPath} {k: K} {k': K} (contains': ISContains (issingleton index k) k'): eqS (index k) (index k').
Proof.
  apply imcontains_singleton in contains'.
  assumption.
Qed.
Lemma issingleton_contains {K: Type} {index: K -> BPath} (k: K): ISContains (issingleton index k) k.
  apply imsingleton_contains.
Qed.

Lemma iset_cwf (trunk: BTrunk) {K: Type} {index: K -> BPath} {KV P: K -> SProp} (set: ISet index): (ISForallS KV P set) -> (forall k: K, KV k -> P k -> BTContains trunk (index k)) -> CoAcc (fun set set': ISet index => existsTSP k: K, AndS (KV k) (P k) & ISExtends set k set') set.
Proof.
  intros pset ptrunk.
  induction (imap_cwf trunk KV (fun k _ => P k) (fun _ _ => False) set) as [ set _ IHset ].
  + constructor.
    intros set' [ k [ kv p ] [ ncontains extends ] ].
    apply IHset.
    - exists k; try assumption.
      exists tt; try assumption.
      repeat split; assumption.
    - eapply isforallS_extend; try eassumption.
      split; assumption.
  + assumption.
  + intros k [ ] kv p.
    split.
    - constructor.
      apply ptrunk; assumption.
    - constructor.
      intros _ [ ].
Qed.



(* An indexed finite subset of pairs, akin to an indexed map *)
Definition IPairSet {K: Type} (kindex: K -> BPath) {V: Type} (vindex: V -> BPath): Type
:= IMap kindex (ISet vindex).
Definition IPSForallS {K: Type} {kindex: K -> BPath} (KV: K -> SProp) {V: Type} {vindex: V -> BPath} (VV: V -> SProp) (P: K -> V -> SProp): IPairSet kindex vindex -> SProp
:= BTreeForallS (fun k vset => ISForallS VV (fun v => AndS (KV k) (P k v)) vset).
Definition IPSContains {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} (set: IPairSet kindex vindex) (k: K) (v: V): SProp
:= existsSS contains: IMContains set k, ISContains (imget_contained set k contains) v.
(* IPSExtends is a non-strict property because it is often used for termination, and Rocq can only structurally recurse on non-strict propositions.
 * It indicates that the latter set is the former set extended with the given previously-absent pair.
 *)
Definition IPSExtends {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} (set: IPairSet kindex vindex) (k: K) (v: V) (set': IPairSet kindex vindex): Prop
:= exists2 vset': ISet vindex,
   IMExtends set k vset' set'
 & match imget set k with
   | None => issingleton vindex v = vset'
   | Some vset => ISExtends vset v vset'
   end.
Definition ipsempty {K: Type} (kindex: K -> BPath) {V: Type} (vindex: V -> BPath): IPairSet kindex vindex
:= imempty kindex (ISet vindex).
(* ipsadd is the key function for conceptually mutating an indexed pair set.
 * One provides it with a set and a pair.
 * Then it either returns the corresponding updated set or an indication that the pair was already present in the set.
 *)
Definition ipsadd {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} (set: IPairSet kindex vindex) (k: K) (v: V): option (IPairSet kindex vindex)
:= imupdate set k (fun vset => match vset with None => Some (issingleton vindex v) | Some vset => isadd vset v end).
Definition ipsget_values {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} (set: IPairSet kindex vindex) (k: K): list V
:= match imget set k with
   | None => nil
   | Some vset => isvalues vset
   end.

Lemma ipsempty_ncontains {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} {k: K} {v: V}: IPSContains (ipsempty kindex vindex) k v -> FalseS.
Proof.
  unfold IPSContains.
  unfold ipsempty.
  intros [ contains _ ].
  apply imempty_ncontains in contains.
  assumption.
Qed.

Lemma ipsextends_ncontains {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} {set: IPairSet kindex vindex} {k: K} {v: V} {set': IPairSet kindex vindex}: IPSExtends set k v set' -> IPSContains set k v -> False.
Proof.
  unfold IPSExtends.
  unfold IPSContains.
  intros [ vset' extends vextends ] [ contains vcontains ].
  pose proof (imget_contains set k) as contains'.
  destruct (imget set k) as [ v' | ].
  + unfold ISExtends in vextends.
    apply vextends.
    destruct contains' as [ contains' e ].
    merge contains contains'.
    destruct e.
    assumption.
  + apply contains'.
    assumption.
Qed.
Lemma ipsextends_contains {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} {set: IPairSet kindex vindex} {k: K} {v: V} {set': IPairSet kindex vindex}: IPSExtends set k v set' -> forall {k': K} {v': V}, IPSContains set k' v' -> IPSContains set' k' v'.
Proof.
  unfold IPSExtends.
  unfold IPSContains.
  intros [ vset' kextends vextends ] k' v' [ kcontains' vcontains' ].
  exists (imextends_contains kextends kcontains').
  destruct (decidableS (eqS (kindex k) (kindex k'))) as [ e | ne ].
  + unfold imget_contained.
    apply eqS_eq in e.
    generalize (imextends_contains kextends kcontains').
    revert kcontains' vcontains'.
    unfold imget_contained.
    unfold IMContains.
    destruct e.
    clear k'.
    intros kcontains vcontains' kcontains'.
    rewrite (bget_contained_extends_eq kextends).
    cbn.
    rewrite (imget_contained_imget kcontains) in vextends.
    apply (isextends_contains vextends).
    assumption.
  + rewrite (imget_contained_extends_neq kextends ne).
    assumption.
Qed.
Lemma ipsextends_contains_pair {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} {set: IPairSet kindex vindex} {k: K} {v: V} {set': IPairSet kindex vindex}: IPSExtends set k v set' -> IPSContains set' k v.
Proof.
  intros [ vset' kextends vextends ].
  exists (imextends_contains_key kextends).
  rewrite (imget_contained_extends_eq kextends).
  pose proof (imget_contains set k) as kcontains.
  destruct (imget set k) as [ vset | ].
  + destruct kcontains as [ kcontains e ].
    destruct e.
    apply (isextends_contains_key vextends).
  + destruct vextends.
    apply issingleton_contains.
Qed.
Lemma ipscontains_extends {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} {set: IPairSet kindex vindex} {k: K} {v: V} {set': IPairSet kindex vindex}: IPSExtends set k v set' -> forall {k': K} {v': V}, IPSContains set' k' v' -> OrS (AndS (eqS (kindex k) (kindex k')) (eqS (vindex v) (vindex v'))) (IPSContains set k' v').
Proof.
  intros [ vset' kextends vextends ] k' v' [ kcontains' vcontains' ].
  destruct (decidableS (eqS (kindex k) (kindex k'))) as [ ek | nek ].
  + revert kcontains' vcontains'.
    unfold IPSContains.
    unfold IMContains.
    unfold imget_contained.
    destruct ek.
    clear k'.
    fold (IMContains set k).
    fold (IMContains set' k).
    intro kcontains'.
    fold (imget_contained set' k kcontains').
    intro vcontains'.
    rewrite (imget_contained_extends_eq kextends) in vcontains'.
    pose proof (imget_contains set k) as kcontains.
    destruct (imget set k) as [ vset | ].
    - destruct kcontains as [ kcontains e ].
      destruct e.
      apply (iscontains_extends vextends) in vcontains'.
      destruct vcontains' as [ ev | vcontains ].
      * left.
        split; try reflexivity.
        assumption.
      * right.
        exists kcontains.
        assumption.
    - left.
      split; try reflexivity.
      destruct vextends.
      apply iscontains_singleton in vcontains'.
      assumption.
  + rewrite (imget_contained_extends_neq kextends nek) in vcontains'.
    right.
    eexists.
    eassumption.
Qed.

Lemma ipsadd_extends {K: Type} {kindex: K -> BPath} {V: Type} {vindex: V -> BPath} (set: IPairSet kindex vindex) (k: K) (v: V): match ipsadd set k v with None => Box (IPSContains set k v) | Some set' => IPSExtends set k v set' end.
Proof.
  unfold ipsadd.
  pose proof (imupdate_extends set k (fun vset => match vset with None => Some (issingleton vindex v) | Some vset' => isadd vset' v end) (fun vset => Box (ISContains vset v)) (eq (issingleton vindex v)) (fun vset vset' => ISExtends vset v vset')) as extends.
  simpl in extends.
  match goal with extends: ?P -> _ |- _ => assert P as p by reflexivity; specialize (extends p); clear p end.
  match goal with extends: ?P -> _ |- _ => assert P as p by (intro vset; apply isadd_extends); specialize (extends p); clear p end.
  destruct (imupdate set k  (fun vset => match vset with None => Some (issingleton vindex v) | Some vset' => isadd vset' v end)).
  + unfold IPSExtends.
    assumption.
  + unfold IPSContains.
    constructor.
    destruct extends as [ contains [ contains' ] ].
    exists contains.
    assumption.
Qed.

Lemma ipsforallS_forall {K: Type} {kindex: K -> BPath} {KV: K -> SProp} {V: Type} {vindex: V -> BPath} {VV: V -> SProp} {P: K -> V -> SProp}: (forall k k': K, KV k -> KV k' -> eqS (kindex k) (kindex k') -> k = k') -> (forall v v': V, VV v -> VV v' -> eqS (vindex v) (vindex v') -> v = v') -> forall {set: IPairSet kindex vindex}, IPSForallS KV VV P set -> forall k: K, KV k -> forall v: V, VV v -> IPSContains set k v -> P k v.
Proof.
  intros kv_inj vv_inj set fa k kv v vv contains.
  unfold IPSForallS in fa.
  unfold IPSContains in contains.
  destruct contains as [ kcontains vcontains ].
  apply btforallS_forall with (kindex k) (bget_contained set (kindex k) kcontains) in fa; try (exists kcontains; reflexivity).
  apply (isforallS_forall vv_inj) with v in fa; try assumption.
  destruct fa as [ kv' p ].
  replace (bget_contained set (kindex k) kcontains).(bekey) with k in p; try assumption.
  symmetry.
  apply kv_inj; try assumption.
  apply (bget_contained set (kindex k) kcontains).(bekeyP).
Qed.

Lemma ipsforallS_mono' {K: Type} {kindex: K -> BPath} {KV KV': K -> SProp} {V: Type} {vindex: V -> BPath} {VV VV': V -> SProp} (P P': K -> V -> SProp) (set: IPairSet kindex vindex): (forall k: K, KV k -> KV' k) -> (forall v: V, VV v -> VV' v) -> (forall key: K, forall v: V, KV key -> VV v -> P key v -> P' key v) -> IPSForallS KV VV P set -> IPSForallS KV' VV' P' set.
Proof.
  intros kk' vv' pp'.
  apply btforallS_mono.
  intros k vset.
  apply isforallS_mono'; try assumption.
  intros v vv [ kv p ].
  split; auto.
Qed.
Lemma ipsforallS_mono {K: Type} {kindex: K -> BPath} {KV: K -> SProp} {V: Type} {vindex: V -> BPath} {VV: V -> SProp} (P P': K -> V -> SProp) (set: IPairSet kindex vindex): (forall key: K, forall v: V, KV key -> VV v -> P key v -> P' key v) -> IPSForallS KV VV P set -> IPSForallS KV VV P' set.
Proof.
  apply ipsforallS_mono'; trivial.
Qed.

Lemma ipsforallS_empty {K: Type} {kindex: K -> BPath} {KV: K -> SProp} {V: Type} {vindex: V -> BPath} {VV: V -> SProp} {P: K -> V -> SProp}: IPSForallS KV VV P (ipsempty kindex vindex).
Proof.
  unfold IPSForallS.
  unfold ipsempty.
  unfold imempty.
  simpl.
  split.
Qed.
Lemma ipsforallS_extend {K: Type} {kindex: K -> BPath} {KV: K -> SProp} {V: Type} {vindex: V -> BPath} {VV: V -> SProp} {P: K -> V -> SProp}: (forall k k': K, KV k -> KV k' -> eqS (kindex k) (kindex k') -> k = k') -> (forall v v': V, VV v -> VV v' -> eqS (vindex v) (vindex v') -> v = v') -> forall {set: IPairSet kindex vindex} {k': K} {v': V} {set': IPairSet kindex vindex}, IPSExtends set k' v' set' -> IPSForallS KV VV P set -> KV k' -> VV v' -> P k' v' -> IPSForallS KV VV P set'.
Proof.
  intros kv_inj vv_inj set k' v' set' [ vset' kextends vextends ] fa kv' vv' p'.
  eapply btforallS_extend in kextends; try eassumption; clear kextends.
  simpl.
  pose proof (imget_contains set k') as kcontains.
  destruct (imget set k') as [ vset | ].
  + destruct kcontains as [ kcontains e ].
    destruct e.
    eapply isforallS_extend; try eassumption; clear vextends; try (split; assumption).
    unfold IPSForallS in fa.
    pose proof (btforallS_forall fa (kindex k') (bget_contained set (kindex k') kcontains)) as fa'.
    simpl in fa'.
    unfold BTreeContains in fa'.
    specialize (fa' (ex_introSS _ _ kcontains (eqS_refl _))).
    revert fa'.
    apply isforallS_mono.
    intros v vv [ kv p ].
    split; try assumption.
    replace k' with (bget_contained set (kindex k') kcontains).(bekey); try assumption.
    apply kv_inj; try assumption.
    apply (bget_contained set (kindex k') kcontains).(bekeyP).
  + destruct vextends.
    apply isforallS_singleton; try assumption.
    split; assumption.
Qed.

Lemma ipsvalues_contains {K: Type} {kindex: K -> BPath} {KV: K -> SProp} {V: Type} {vindex: V -> BPath} {VV: V -> SProp} {P: K -> V -> SProp} {set: IPairSet kindex vindex}: (forall k k': K, KV k -> KV k' -> eqS (kindex k) (kindex k') -> k = k') -> (forall v v': V, VV v -> VV v' -> eqS (vindex v) (vindex v') -> v = v') -> IPSForallS KV VV P set -> forall k: K, KV k -> forall v: V, VV v -> IPSContains set k v -> ListContains v (ipsget_values set k).
Proof.
  intros kv_inj vv_inj fa k kv v vv contains.
  unfold IPSForallS in fa.
  unfold IPSContains in contains.
  destruct contains as [ kcontains vcontains ].
  pose proof (btforallS_forall fa _ (bget_contained set (kindex k) kcontains) (ex_introSS _ _ kcontains (eqS_refl _))) as fa'.
  simpl in fa'.
  unfold ipsget_values.
  pose proof (imget_contains set k) as kcontains'.
  destruct (imget set k) as [ vset | ].
  + destruct kcontains' as [ kcontains' e ].
    merge kcontains kcontains'.
    destruct e.
    apply (isvalues_contains vv_inj fa'); assumption.
  + destruct (kcontains' kcontains).
Qed.
Lemma ipscontains_values {K: Type} {kindex: K -> BPath} {KV: K -> SProp} {V: Type} {vindex: V -> BPath} {VV: V -> SProp} {P: K -> V -> SProp} {set: IPairSet kindex vindex}: IPSForallS KV VV P set -> forall k: K, KV k -> forall v: V, ListContains v (ipsget_values set k) -> AndS (VV v) (IPSContains set k v).
Proof.
  intros fa k kv v vcontains.
  unfold ipsget_values in vcontains.
  pose proof (imget_contains set k) as kcontains.
  destruct (imget set k) as [ vset | ]; [ | inversion vcontains ].
  destruct kcontains as [ kcontains e ].
  destruct e.
  unfold IPSForallS in fa.
  pose proof (btforallS_forall fa (kindex k) (bget_contained set (kindex k) kcontains)) as fa'.
  specialize (fa' (ex_introSS _ _ kcontains (eqS_refl _))).
  simpl in fa'.
  apply (iscontains_values fa') in vcontains.
  destruct vcontains as [ vv vcontains ].
  split; try assumption.
  unfold IPSContains.
  exists kcontains.
  assumption.
Qed.

Lemma ipairset_cwf (ktrunk: BTrunk) (vtrunk: BTrunk) {K: Type} {kindex: K -> BPath} {KV: K -> SProp} {V: Type} {vindex: V -> BPath} {VV: V -> SProp} {P: K -> V -> SProp}: (forall k k': K, KV k -> KV k' -> eqS (kindex k) (kindex k') -> k = k') -> (forall v v': V, VV v -> VV v' -> eqS (vindex v) (vindex v') -> v = v') -> (forall k: K, KV k -> BTContains ktrunk (kindex k)) -> (forall v: V, VV v -> BTContains vtrunk (vindex v)) -> forall set: IPairSet kindex vindex, (IPSForallS KV VV P set) -> CoAcc (fun set set': IPairSet kindex vindex => existsTSP k: K, KV k & existsTSP v: V, AndS (VV v) (P k v) & IPSExtends set k v set') set.
Proof.
  intros kv_inj vv_inj kv_trunk vv_trunk.
  assert (forall path, forall entry: BEntry K (fun _ => ISet vindex) (fun k => eqS (kindex k) path), ISForallS VV (fun _ => TrueS) entry.(bevalue) -> CoAcc (fun entry entry': BEntry K (fun _ => ISet vindex) (fun k => eqS (kindex k) path) => existsTSP v: V, VV v & ISExtends entry.(bevalue) v entry'.(bevalue)) entry) as entry_cwf.
  + intros path entry.
    generalize (eq_refl entry.(bevalue)).
    generalize entry.(bevalue) at 2 3.
    intros vset evset vfa.
    revert entry evset.
    induction (iset_cwf vtrunk vset vfa) as [ vset _ IHvset ]; try auto.
    intros entry e.
    destruct e.
    constructor.
    intros entry' [ v vv vextends ].
    apply IHvset with entry'.(bevalue); try reflexivity.
    - exists v; try assumption.
      repeat split.
      assumption.
    - eapply isforallS_extend; try eassumption.
      split.
  + intros set kfa.
    induction (bextends_cwf ktrunk (fun path (entry: BEntry K (fun _ => ISet vindex) (fun k => eqS (kindex k) path)) => Box (KV entry.(bekey)) /\ Box (ISForallS VV (fun _ => TrueS) entry.(bevalue))) (fun path (entry entry': BEntry K (fun _ => ISet vindex) (fun k => eqS (kindex k) path)) => existsTSP v: V, VV v & ISExtends entry.(bevalue) v entry'.(bevalue)) set) as [ set _ IHset ].
    - constructor.
      intros set' [ k kv [ v [ vv p ] extends ] ].
      apply IHset; clear IHset.
      * exists (kindex k); try (apply kv_trunk; assumption).
        destruct extends as [ vset' extends vextends ].
        pose proof (imget_contains set k) as contains.
        exists {| bekey := k; bevalue := vset'; bekeyP := eqS_refl (kindex k) |}; repeat split; try assumption.
        unfold imget in *.
        destruct (bget set (kindex k)) as [ vset | ]; simpl in *.
        ** destruct contains as [ contains e ].
           destruct e.
           apply btforallS_get_contained with (contains := contains) in kfa.
           exists v; assumption.
        ** destruct vextends.
           split; constructor; try assumption.
           apply isforallS_singleton; try assumption.
           split.
      * eapply ipsforallS_extend; eassumption.
    - intros path entry [ [ kv ] [ vfa ] ].
      apply entry_cwf.
      assumption.
    - intros path contains.
      apply entry_cwf.
      pose proof (btforallS_forall kfa path (bget_contained set path contains)) as vfa.
      simpl in vfa.
      specialize (vfa (ex_introSS _ _ contains (eqS_refl _))).
      eapply isforallS_mono; try eassumption.
      split.
Qed.



(* Part 1.7: Sorts
 * Many definitions conceptually use a sums of types, and operations thereon.
 * For lack of a better term, we encode this pattern using "sorts" and selections/morphism/eliminations thereon.
 * In addition to convenience, this specialized encoding avoids the need to assume functional extensionality even despite Rocq's lack of definitional eta-equivalence for sum types.
 *)
Definition Sort: Type
:= list Type.
Definition SumSort: Sort -> Type
:= fix SumSort (s: Sort): Type
:= match s with
   | nil => Empty
   | cons T s => sum T (SumSort s)
   end.
Definition sortl {T : Type} {s: Sort}: T -> SumSort (cons T s)
:= inl.
Definition sortr {T : Type} {s: Sort}: SumSort s -> SumSort (cons T s)
:= inr.
Definition sorte {T: Type} {s: Sort} {K: Type}: (T -> K) -> (SumSort s -> K) -> SumSort (cons T s) -> K
:= sume.

(* A selection from T maps T to a single type within a sort. *)
Definition SortSelection (T: Type): Sort -> Type
:= fix SortSelection (s: Sort): Type
:= match s with
   | nil => Empty
   | cons T' s => sum (T -> T') (SortSelection s)
   end.
Definition select_head {T T': Type} (f: T -> T') {s: Sort}: SortSelection T (cons T' s)
:= inl f.
Definition extend_selection {T: Type} {s: Sort} (T': Type) (selection: SortSelection T s): SortSelection T (cons T' s)
:= inr selection.

(* A morphism maps each type in the source sort into a single type in the target sort. *)
Definition SortMorphism: Sort -> Sort -> Type
:= fix SortMorphism (s: Sort): Sort -> Type
:= match s with
   | nil => fun _ => unit
   | cons T s => fun s' => prod (SortSelection T s') (SortMorphism s s')
   end.
Definition nil_morphism {s: Sort}: SortMorphism nil s
:= tt.
Definition pair_morphism {T: Type} {s s': Sort} (selection: SortSelection T s') (morphism: SortMorphism s s'): SortMorphism (cons T s) s'
:= pair selection morphism.

(* An elimination onto T maps each type in the sort into T. *)
Definition SortElimination (T: Type): Sort -> Type
:= fix SortElimination (s: Sort): Type
:= match s with
   | nil => unit
   | cons T' s => prod (T' -> T) (SortElimination s)
   end.
Definition nil_elimination {T': Type}: SortElimination T' nil
:= tt.
Definition pair_elimination {T' T: Type} {s: Sort}: (T -> T') -> SortElimination T' s -> SortElimination T' (cons T s)
:= pair.

Definition apply_selection {T: Type}: forall {s: Sort}, SortSelection T s -> T -> SumSort s
:= fix apply_selection {s: Sort}: SortSelection T s -> T -> SumSort s
:= match s with
   | nil => emptye
   | cons T' s => fun selection => match selection with
                                   | inl f => fun t => sortl (f t)
                                   | inr selection => fun t => sortr (apply_selection selection t)
                                   end
   end.
Arguments apply_selection {T !s} !selection.
Definition apply_morphism: forall {s s': Sort}, SortMorphism s s' -> SumSort s -> SumSort s'
:= fix apply_morphism {s: Sort}: forall s': Sort, SortMorphism s s' -> SumSort s -> SumSort s'
:= match s as s return forall s': Sort, SortMorphism s s' -> SumSort s -> SumSort s' with
   | nil => fun _ _ => emptye
   | cons T s => fun s' morphism v => match v with
                                      | inl t => apply_selection (fst morphism) t
                                      | inr v => apply_morphism s' (snd morphism) v
                                      end
   end.
Arguments apply_morphism {!s s'} morphism !v.
Definition apply_elimination {T: Type}: forall {s: Sort}, SortElimination T s -> SumSort s -> T
:= fix apply_elimination {s: Sort}: SortElimination T s -> SumSort s -> T
:= match s with
   | nil => fun _ => emptye
   | cons T' s => fun p v => match v with
                             | inl t' => fst p t'
                             | inr v => apply_elimination (snd p) v
                             end
   end.
Arguments apply_elimination {T !s} elimination !v.

Definition extend_morphism (T: Type) {s': Sort}: forall {s: Sort}, SortMorphism s s' -> SortMorphism s (cons T s')
:= fix extend_morphism {s: Sort}: SortMorphism s s' -> SortMorphism s (cons T s')
:= match s as s return SortMorphism s s' -> SortMorphism s (cons T s')with
   | nil => fun _ => nil_morphism
   | cons T' s => fun morphism => pair_morphism (extend_selection T (fst morphism)) (extend_morphism (snd morphism))
   end.
Definition cons_morphism {T T': Type} (f: T -> T') {s s': Sort} (morphism: SortMorphism s s'): SortMorphism (cons T s) (cons T' s')
:= pair_morphism (select_head f) (extend_morphism T' morphism).
Definition consid_morphism (T: Type): forall {s s': Sort}, SortMorphism s s' -> SortMorphism (cons T s) (cons T s')
:= @cons_morphism T T (fun t => t).

Definition id_morphism: forall {s: Sort}, SortMorphism s s
:= fix id_morphism {s: Sort}: SortMorphism s s
:= match s with
   | nil => nil_morphism
   | cons T s => consid_morphism T id_morphism
   end.

Definition compose_selection {T T': Type} (f: T -> T'): forall {s: Sort}, SortSelection T' s -> SortSelection T s
:= fix compose_selection {s: Sort}: SortSelection T' s -> SortSelection T s
:= match s as s return SortSelection T' s -> SortSelection T s with
   | nil => emptye
   | cons T'' s => fun selection => match selection with
                                    | inl f' => select_head (compose f f')
                                    | inr selection => extend_selection T'' (compose_selection selection)
                                    end
   end.
Definition select_morphism {T: Type}: forall {s: Sort}, SortSelection T s -> forall {s': Sort}, SortMorphism s s' -> SortSelection T s'
:= fix select_morphism {s: Sort}: SortSelection T s -> forall s': Sort, SortMorphism s s' -> SortSelection T s'
:= match s as s return SortSelection T s -> forall {s': Sort}, SortMorphism s s' -> SortSelection T s' with
   | nil => emptye
   | cons T' s => fun selection => match selection with
                                   | inl f => fun s' morphism => compose_selection f (fst morphism)
                                   | inr selection => fun s' morphism => select_morphism selection s' (snd morphism)
                                   end
   end.

Definition compose_morphism: forall {s s' s'': Sort} (morphism: SortMorphism s s') (morphism': SortMorphism s' s''), SortMorphism s s''
:= fix compose_morphism {s: Sort}: forall s' s'': Sort, SortMorphism s s' -> SortMorphism s' s'' -> SortMorphism s s''
:= match s as s return forall s' s'': Sort, SortMorphism s s' -> SortMorphism s' s'' -> SortMorphism s s'' with
   | nil => fun _ _ _ _ => nil_morphism
   | cons T s => fun s' s'' morphism morphism' => pair_morphism (select_morphism (fst morphism) morphism') (compose_morphism s' s'' (snd morphism) morphism')
   end.

Definition compose_elimination {T': Type}: forall {s: Sort}, SortElimination T' s -> forall {T'': Type}, (T' -> T'') -> SortElimination T'' s
:= fix compose_elimination {s: Sort}: SortElimination T' s -> forall T'': Type, (T' -> T'') -> SortElimination T'' s
:= match s with
   | nil => fun _ _ _ => nil_elimination
   | cons T s => fun elimination T'' f' => pair_elimination (compose (fst elimination) f') (compose_elimination (snd elimination) T'' f')
   end.
Definition eliminate_selection {T: Type} {s': Sort} (selection: SortSelection T s') {T'': Type} (elimination: SortElimination T'' s') (t: T): T''
:= apply_elimination elimination (apply_selection selection t).
Definition eliminate_morphism: forall {s s': Sort}, SortMorphism s s' -> forall {T'': Type}, SortElimination T'' s' -> SortElimination T'' s
:= fix eliminate_morphism {s: Sort}: forall s': Sort, SortMorphism s s' -> forall T'': Type, SortElimination T'' s' -> SortElimination T'' s
:= match s as s return forall s': Sort, SortMorphism s s' -> forall T'': Type, SortElimination T'' s' -> SortElimination T'' s with
   | nil => fun s' _ T'' _ => nil_elimination
   | cons T s => fun s' morphism T'' elimination => pair_elimination (eliminate_selection (fst morphism) elimination) (eliminate_morphism s' (snd morphism) T'' elimination)
   end.
Definition eliminate_sum {T: Type}: forall {s: Sort}, (SumSort s -> T) -> SortElimination T s
:= fix eliminate_sum {s: Sort}: (SumSort s -> T) -> SortElimination T s
:= match s with
   | nil => fun _ => nil_elimination
   | cons T s => fun f => pair_elimination (compose sortl f) (eliminate_sum (compose sortr f))
   end.

Lemma select_extend_morphism (T: Type) {s s': Sort} (selection: SortSelection T s) (T': Type) (morphism: SortMorphism s s'): select_morphism selection (extend_morphism T' morphism) = extend_selection T' (select_morphism selection morphism).
Proof.
  induction s; simpl in *.
  + destruct selection.
  + destruct selection as [ f | selection ]; simpl.
    - reflexivity.
    - apply IHs.
Qed.

Lemma apply_compose_selection {T T': Type} {s: Sort} (f: T -> T') (selection: SortSelection T' s) (t: T): apply_selection (compose_selection f selection) t = apply_selection selection (f t).
Proof.
  induction s; simpl in *.
  + destruct selection.
  + destruct selection as [ f' | selection ]; simpl.
    - reflexivity.
    - f_equal.
      apply IHs.
Qed.
Lemma apply_select_morphism {T: Type} {s s': Sort} (selection: SortSelection T s) (morphism: SortMorphism s s') (t: T): apply_selection (select_morphism selection morphism) t = apply_morphism morphism (apply_selection selection t).
Proof.
  induction s; simpl in *.
  + destruct selection.
  + destruct selection as [ f | selection ].
    - apply apply_compose_selection.
    - apply IHs.
Qed.
Lemma apply_extend_morphism (T: Type) {s s': Sort} (morphism: SortMorphism s s') (v: SumSort s): apply_morphism (extend_morphism T morphism) v = inr (apply_morphism morphism v).
Proof.
  induction s; simpl in *.
  + destruct v.
  + destruct v as [ t | v ].
    - reflexivity.
    - apply IHs.
Qed.
Lemma apply_compose_morphism {s s' s'': Sort} (morphism: SortMorphism s s') (morphism': SortMorphism s' s'') (v: SumSort s): apply_morphism (compose_morphism morphism morphism') v = apply_morphism morphism' (apply_morphism morphism v).
Proof.
  induction s; simpl in *.
  + destruct v.
  + destruct v as [ t | v ].
    - apply apply_select_morphism.
    - apply IHs.
Qed.
Lemma apply_compose_elimination {s: Sort} {T' T'': Type} (elimination: SortElimination T' s) (f': T' -> T'') (v: SumSort s): apply_elimination (compose_elimination elimination f') v = f' (apply_elimination elimination v).
Proof.
  induction s; simpl.
  + destruct v.
  + destruct v as [ t | v ].
    - reflexivity.
    - apply IHs.
Qed.
Lemma apply_eliminate_morphism {s s': Sort} {T'': Type} (morphism: SortMorphism s s') (elimination: SortElimination T'' s') (v: SumSort s): apply_elimination (eliminate_morphism morphism elimination) v = apply_elimination elimination (apply_morphism morphism v).
Proof.
  induction s; simpl.
  + destruct v.
  + destruct v as [ t | v ].
    - reflexivity.
    - apply IHs.
Qed.
Lemma apply_eliminate_sum {T': Type} {s: Sort} (f: SumSort s -> T') (v: SumSort s): apply_elimination (eliminate_sum f) v = f v.
Proof.
  induction s; simpl in *.
  + destruct v.
  + destruct v as [ t | v ].
    - reflexivity.
    - apply IHs.
Qed.

Lemma compose_id_selection (T: Type) {s: Sort} (selection: SortSelection T s): compose_selection (fun t: T => t) selection = selection.
Proof.
  induction s; simpl in *.
  + destruct selection.
  + destruct selection as [ f | selection ]; simpl.
    - reflexivity.
    - unfold extend_selection.
      f_equal.
      apply IHs.
Qed.

Lemma compose_morphism_extend {s s' s'': Sort} (morphism: SortMorphism s s') (T: Type) (morphism': SortMorphism s' s''): compose_morphism morphism (extend_morphism T morphism') = extend_morphism T (compose_morphism morphism morphism').
Proof.
  induction s; simpl.
  + reflexivity.
  + unfold pair_morphism.
    f_equal.
    - apply select_extend_morphism.
    - apply IHs.
Qed.
Lemma compose_extend_pair_morphism (T': Type) {s s' s'': Sort} (morphism: SortMorphism s s') (selection': SortSelection T' s'') (morphism': SortMorphism s' s''): compose_morphism (extend_morphism T' morphism) (pair_morphism selection' morphism') = compose_morphism morphism morphism'.
Proof.
  induction s; simpl.
  + reflexivity.
  + f_equal.
    apply IHs.
Qed.
Lemma compose_pair_morphism {T: Type} {s s' s'': Sort} (selection: SortSelection T s') (morphism: SortMorphism s s') (morphism': SortMorphism s' s''): compose_morphism (pair_morphism selection morphism) morphism' = pair_morphism (select_morphism selection morphism') (compose_morphism morphism morphism').
Proof.
  reflexivity.
Qed.
Lemma compose_cons_pair_morphism {T T': Type} (f: T -> T') {s s' s'': Sort} (morphism: SortMorphism s s') (selection': SortSelection T' s'') (morphism': SortMorphism s' s''): compose_morphism (cons_morphism f morphism) (pair_morphism selection' morphism') = pair_morphism (compose_selection f selection') (compose_morphism morphism morphism').
Proof.
  unfold cons_morphism.
  rewrite compose_pair_morphism.
  f_equal.
  apply compose_extend_pair_morphism.
Qed.
Lemma compose_consid_pair_morphism (T: Type) {s s' s'': Sort} (morphism: SortMorphism s s') (selection': SortSelection T s'') (morphism': SortMorphism s' s''): compose_morphism (consid_morphism T morphism) (pair_morphism selection' morphism') = pair_morphism selection' (compose_morphism morphism morphism').
Proof.
  unfold consid_morphism.
  rewrite compose_cons_pair_morphism.
  f_equal.
  apply compose_id_selection.
Qed.
Lemma compose_cons_cons_morphism {T T' T'': Type} (f: T -> T') (f': T' -> T'') {s s' s'': Sort} (morphism: SortMorphism s s') (morphism': SortMorphism s' s''): compose_morphism (cons_morphism f morphism) (cons_morphism f' morphism') = cons_morphism (compose f f') (compose_morphism morphism morphism').
Proof.
  unfold cons_morphism at 2 3.
  rewrite compose_cons_pair_morphism.
  f_equal.
  apply compose_morphism_extend.
Qed.
Lemma compose_consid_consid_morphism (T: Type) {s s' s'': Sort} (morphism: SortMorphism s s') (morphism': SortMorphism s' s''): compose_morphism (consid_morphism T morphism) (consid_morphism T morphism') = consid_morphism T (compose_morphism morphism morphism').
Proof.
  unfold consid_morphism.
  apply compose_cons_cons_morphism.
Qed.

Lemma eliminate_extend_selection_pair_elimination {s': Sort} {T T' T'': Type} (f': T' -> T'') (selection: SortSelection T s') (elimination': SortElimination T'' s'): eliminate_selection (extend_selection T' selection) (pair_elimination f' elimination') = eliminate_selection selection elimination'.
Proof.
  reflexivity.
Qed.
Lemma eliminate_extend_morphism_pair_elimination {s s': Sort} {T' T'': Type} (f': T' -> T'') (morphism: SortMorphism s s') (elimination': SortElimination T'' s'): eliminate_morphism (extend_morphism T' morphism) (pair_elimination f' elimination') = eliminate_morphism morphism elimination'.
Proof.
  induction s; simpl.
  + reflexivity.
  + rewrite eliminate_extend_selection_pair_elimination.
    f_equal.
    apply IHs.
Qed.
Lemma eliminate_nil_morphism {s': Sort} {T'': Type} (elimination': SortElimination T'' s'): eliminate_morphism nil_morphism elimination' = nil_elimination.
Proof.
  reflexivity.
Qed.
Lemma eliminate_pair_morphism {s s': Sort} {T T'': Type} (selection: SortSelection T s') (morphism: SortMorphism s s') (elimination': SortElimination T'' s'): eliminate_morphism (pair_morphism selection morphism) elimination' = pair_elimination (eliminate_selection selection elimination') (eliminate_morphism morphism elimination').
Proof.
  reflexivity.
Qed.
Lemma eliminate_cons_pair_elimination {s s': Sort} {T T' T'': Type} (f : T -> T') (f': T' -> T'') (morphism: SortMorphism s s') (elimination': SortElimination T'' s'): eliminate_morphism (cons_morphism f morphism) (pair_elimination f' elimination') = pair_elimination (compose f f') (eliminate_morphism morphism elimination').
Proof.
  simpl.
  f_equal.
  apply eliminate_extend_morphism_pair_elimination.
Qed.
Lemma eliminate_consid_pair_elimination {s s': Sort} {T T'': Type} (f': T -> T'') (morphism: SortMorphism s s') (elimination': SortElimination T'' s'): eliminate_morphism (consid_morphism T morphism) (pair_elimination f' elimination') = pair_elimination f' (eliminate_morphism morphism elimination').
Proof.
  simpl.
  f_equal.
  apply eliminate_extend_morphism_pair_elimination.
Qed.
Lemma eliminate_select_head_pair_elimination {s': Sort} {T T' T'': Type} (f: T -> T') (f': T' -> T'') (elimination': SortElimination T'' s'): eliminate_selection (select_head f) (pair_elimination f' elimination') = compose f f'.
Proof.
  reflexivity.
Qed.
Lemma eliminate_id_morphism {s: Sort} {T': Type} (elimination: SortElimination T' s): eliminate_morphism id_morphism elimination = elimination.
Proof.
  induction s; simpl.
  + destruct elimination.
    reflexivity.
  + destruct elimination as [ f elimination ].
    unfold pair_elimination.
    f_equal.
    fold (pair_elimination f elimination).
    rewrite eliminate_extend_morphism_pair_elimination.
    apply IHs.
Qed.

Lemma compose_pair_elimination {T T' T'': Type} {s: Sort} (f: T -> T') (elimination: SortElimination T' s) (f': T' -> T''): compose_elimination (pair_elimination f elimination) f' = pair_elimination (compose f f') (compose_elimination elimination f').
Proof.
  reflexivity.
Qed.
Lemma compose_compose_elimination {s: Sort} {T' T'' T''': Type} (elimination: SortElimination T' s) (f': T' -> T'') (f'': T'' -> T'''): compose_elimination (compose_elimination elimination f') f'' = compose_elimination elimination (compose f' f'').
Proof.
  induction s; simpl.
  + reflexivity.
  + f_equal.
    apply IHs.
Qed.



(* A class for sorts comprised entirely of subcountable types *)
Definition SubCountableSort: Sort -> Type
:= fix SubCountableSort (sort: Sort): Type
:= match sort with
   | nil => Unit
   | cons T sort => prod (SubCountable T) (SubCountableSort sort)
   end.
Existing Class SubCountableSort.

#[local] Instance nil_SubCountableSort: SubCountableSort nil
:= tt.
#[local] Instance cons_SubCountableSort (T: Type) {T_SubCountable: SubCountable T} (sort: Sort) {sort_SubCountable: SubCountableSort sort}: SubCountableSort (cons T sort)
:= pair T_SubCountable sort_SubCountable.

#[local] Instance SumSort_SubCountable: forall (sort: Sort) `{SubCountableSort sort}, SubCountable (SumSort sort)
:= fix SumSort_SubCountable (sort: Sort): SubCountableSort sort -> SubCountable (SumSort sort)
:= match sort as sort return SubCountableSort sort -> SubCountable (SumSort sort) with
   | nil => fun _ => Empty_SubCountable
   | cons T sort => fun sc => @sum_SubCountable _ _ (fst sc) (SumSort_SubCountable sort (snd sc))
   end.

(* A class for sorts comprised entirely of subfinite types *)
Definition SubFiniteSort: Sort -> Type
:= fix SubFiniteSort (sort: Sort): Type
:= match sort with
   | nil => Unit
   | cons T sort => prod (SubFinite T) (SubFiniteSort sort)
   end.
Existing Class SubFiniteSort.

#[local] Instance SubFiniteSort_SubCountableSort: forall (sort: Sort), SubFiniteSort sort -> SubCountableSort sort
:= fix SubFiniteSort_SubCountableSort (sort: Sort): SubFiniteSort sort -> SubCountableSort sort
:= match sort as sort return SubFiniteSort sort -> SubCountableSort sort with
   | nil => fun _ => nil_SubCountableSort
   | cons T sort => fun sf => @cons_SubCountableSort T (fst sf).(SubFinite_SubCountable) sort (SubFiniteSort_SubCountableSort sort (snd sf))
   end.

#[local] Instance nil_SubFiniteSort: SubFiniteSort nil
:= tt.
#[local] Instance cons_SubFiniteSort (T: Type) {T_SubFinite: SubFinite T} (sort: Sort) {sort_SubFinite: SubFiniteSort sort}: SubFiniteSort (cons T sort)
:= pair T_SubFinite sort_SubFinite.

#[local] Instance SumSort_SubFinite: forall sort: Sort, forall {sort_SubFinite: SubFiniteSort sort}, SubFinite (SumSort sort)
:= fix SumSort_SubFinite (sort: Sort): SubFiniteSort sort -> SubFinite (SumSort sort)
:= match sort as sort return SubFiniteSort sort -> SubFinite (SumSort sort) with
   | nil => fun _ => Empty_SubFinite
   | cons T sort => fun sc => @sum_SubFinite _ _ (fst sc) (SumSort_SubFinite sort (snd sc))
   end.

Lemma SumSort_SubFinite_SubCountable (sort: Sort) {sort_Finite: SubFiniteSort sort}: (@SumSort_SubFinite sort sort_Finite).(SubFinite_SubCountable) = @SumSort_SubCountable sort (SubFiniteSort_SubCountableSort sort sort_Finite).
Proof.
  induction sort; simpl.
  + reflexivity.
  + f_equal.
    apply IHsort.
Qed.



(* Part 2: Programs
 * Here we define effectively the syntax of expressions, user types, and programs.
 * This corresponds to Figure 6 of the paper.
 * Unlike the paper though, the hierarchy of interfaces is formalized algebraically.
 * This permits infinite sets of interfaces, which enables interfaces encoding many common structural types.
 * Furthermore, the namespaces of interface and methods, along with their respective arities, is also specified algebraically.
 * This permits interfaces and methods with infinite arities.
 * Many definitions, as well as the proof of safety, extend to scuh infinite settings.
 * Nonetheless, parts of the algorithm only work in finitary settings, and these parts will be explicitly parameterized with such requirements.
 *)

(* Part 2.1: Schemes *)
(* A Scheme specifies the Interface and Method names in the program, along with types representing the arities of each Interface or Method (unlike the paper, we allow methods to have an arbitrary amount of parameters).
 * For example, given a hierarchy in the paper, Interface would be the subset of names declared in the hierarchy, and Method would be the product of arbitrary strings and nats.
 * IParameter, then, would be the subset of type parameters declared for a given interface in the hierarchy, and MInput would be a type whose cardinality corresponds to its nat.
 * Method is required to be SubCountable so that object-instantiation expressions can be defined using an SCSet of the methods declared in the object.
 * By using IParameter and MInput, rather than lists of types and methods, we make our mechanization both simpler and more general.
 * This does mean that arity-matching is automatically guaranteed rather than performed by our validation algorithm, but this is not an interesting aspect of our contributations.
 *)
Record Scheme: Type :=
{ Interface: Type;
  IParameter (interface: Interface): Type;
  Method: Type;
  Method_SubCountable :: SubCountable Method;
  MInput (method: Method): Type;
}.



(* We fix a global Scheme, and we never use any other Scheme in the following. *)
Parameter scheme: Scheme.



(* Part 2.2: Expressions *)
(* Expression is parameterized by a Sort representing the variables that are in scope.
 * This means (program) variable uses are guaranteed to be in scope.
 * Similarly, our use of Schemes ensures that invocations and method implementations are guaranteed to have the correct number of arguments and parameters.
 *)
Inductive Expression | {Input: Sort}: Type
:= einput (input: SumSort Input)
 | einvoke (receiver: Expression) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> Expression)
 | eobject (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> Expression (Input := cons (scheme.(MInput) method) Input)).
Arguments Expression : clear implicits.

Definition AExpression (Input: Sort): Type
:= forall Input': Sort, (SumSort Input -> SumSort Input') -> Expression Input'.
Definition econcretize {Input: Sort} (expression: AExpression Input): Expression Input
:= expression Input (fun input => input).
Definition eabstract: forall {Input: Sort}, Expression Input -> AExpression Input
:= fix eabstract {Input: Sort} (expression: Expression Input): AExpression Input
:= match expression with
   | einput input => fun Input' naming => einput (naming input)
   | einvoke receiver method arguments => fun Input' naming => einvoke (eabstract receiver Input' naming) method (fun input => eabstract (arguments input) Input' naming)
   | eobject interface methods bodies => fun Input' naming => eobject interface methods (fun method contains => eabstract (bodies method contains) (cons (scheme.(MInput) method) Input') (sum_mapr naming))
   end.

Definition aesubstitute: forall {Input: Sort}, Expression Input -> forall {Input': Sort}, (SumSort Input -> AExpression Input') -> Expression Input'
:= fix aesubstitute {Input: Sort} (expression: Expression Input): forall Input': Sort, (SumSort Input -> AExpression Input') -> Expression Input'
:= match expression with
   | einput input => fun Input' substitution => econcretize (substitution input)
   | einvoke receiver method arguments => fun Input' substitution => einvoke (aesubstitute receiver Input' substitution) method (fun input => aesubstitute (arguments input) Input' substitution)
   | eobject interface methods bodies => fun Input' substitution => eobject interface methods (fun method contains => aesubstitute (bodies method contains) (cons (scheme.(MInput) method) Input') (sorte (fun input => eabstract (einput (sortl input))) (fun input => fun Input' naming => substitution input Input' (fun input => naming (sortr input)))))
   end.
Definition esubstitute {Input: Sort} (expression: Expression Input) {Input': Sort} (substitution: SumSort Input -> Expression Input'): Expression Input'
:= aesubstitute expression (fun input => eabstract (substitution input)).



(* Part 2.3: Operational Semantics *)

(* Any object instantiation is a value. *)
Inductive Value {Input: Sort}: Expression Input -> SProp
:= vobject (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> Expression (cons (scheme.(MInput) method) Input)): Value (eobject interface methods bodies).

(* StepsTo defines the operational semantics of our calculus, in line with Figure 7 of the paper.
 * Only method invocations are reducible.
 * Either the receiver is reduced or, when the receiver is an object instantiation, the invocation is reduced to the corresponding method implementation of the object.
 * Invocation is lazy; arguments are substituted as arbitrary expressions, rather than being reduced to values first.
 * We do this because it is more amenable to our choice to make arity-matching guaranteed using an MInput type rather than using a list and manually performing arity-matching.
 *)
Inductive StepsTo {Input: Sort}: Expression Input -> Expression Input -> SProp
:= step_receiver
     (receiver receiver': Expression Input)
     (method: scheme.(Method))
     (arguments: scheme.(MInput) method -> Expression Input)
      : StepsTo receiver receiver'
     -> StepsTo (einvoke receiver method arguments) (einvoke receiver' method arguments)
 | step_invoke
     (interface: scheme.(Interface))
     (methods: SCSet scheme.(Method))
     (bodies: forall method: scheme.(Method), SCSetContains methods method -> Expression (cons (scheme.(MInput) method) Input))
     (method: scheme.(Method))
     (contains: SCSetContains methods method)
     (arguments: scheme.(MInput) method -> Expression Input)
      : StepsTo (einvoke (eobject interface methods bodies) method arguments)
                (esubstitute (bodies method contains) (sorte arguments einput)).
Arguments StepsTo {_} _ _.



(* Part 2.4: User Types, Signatures, and Hierarchies *)

(* User types are parameterized by the type variables that are in scope.
 * This means type variable uses are guaranteed to be in scope.
 * Similarly, our use of Schemes ensures that interface types are guaranteed to have the correct number of type arguments.
 *)
Inductive UserType {Var: Type}: Type
:= utvariable (variable: Var)
 | utany
 | utinterface (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> UserType).
Arguments UserType : clear implicits.



(* A user method signature assigns a type to each parameter and the result. *)
Record UserMethodSignature {Var: Type} {Input: Type}: Type :=
{ umsinput (input: Input): UserType Var;
  umsresult: UserType Var;
}.
Arguments UserMethodSignature : clear implicits.

(* A user body signature specifies the finite subset of methods that have signatures, along with a user method signature for each method in this subset. *)
Record UserBodySignature {Var: Type}: Type :=
{ ubsmethods: SCSet scheme.(Method);
  ubsmethod (method: scheme.(Method)) (contains: SCSetContains ubsmethods method): UserMethodSignature Var (scheme.(MInput) method);
}.
Arguments UserBodySignature : clear implicits.

(* A user interface signature specifies a variance for each type parameter in scope, along with a user body signature using those type parameters. *)
Record UserInterfaceSignature {Var: Type}: Type :=
{ uisvariance (parameter: Var): Sign;
  uisbody: UserBodySignature Var;
}.
Arguments UserInterfaceSignature : clear implicits.

(* A hierarchy specifies a user interface signature for each interface in the Scheme. *)
Record Hierarchy: Type :=
{ hinterface (interface: scheme.(Interface)): UserInterfaceSignature (scheme.(IParameter) interface);
}.



(* We fix a global Hierarchy, and we never use any other Hierarchy in the following. *)
Parameter hierarchy: Hierarchy.



(* Part 2.5: Programs *)

(* A program uses the global hierarchy and furthermore specifies its closed expression and expected closed type. *)
Record Program: Type :=
{ pexpression: Expression nil;
  ptype: UserType Empty;
}.



(* Part 2.6: User Type, Signature, and Program Validity *)

(* UserVariance indicates when a type has a given variance assuming a given variance on the type parameters in scope.
 * This corresponds to Figure 8 of the paper.
 *)
Inductive UserVariance {Var: Type} {variance: Var -> Sign}: UserType Var -> Sign -> SProp
:= uvvariable (variable: Var): UserVariance (utvariable variable) (variance variable)
 | uvany (sign: Sign): UserVariance utany sign
 | uvinterface (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> UserType Var) (sign: Sign): (forall parameter: scheme.(IParameter) interface, UserVariance (arguments parameter) (multiply sign ((hierarchy.(hinterface) interface).(uisvariance) parameter))) -> UserVariance (utinterface interface arguments) sign.
Arguments UserVariance {_} _ _ _.



(* The following each indicate when variance is respected.
 * They correspond to Figure 9 of the paper.
 *)
Record UserMethodSignatureV {Var Input: Type} {signature: UserMethodSignature Var Input} {variance: Var -> Sign}: SProp :=
{ umsinputv (input: Input): UserVariance variance (signature.(umsinput) input) negative;
  umsresultv: UserVariance variance signature.(umsresult) positive;
}.
Arguments UserMethodSignatureV {_ _} _ _.

Record UserBodySignatureV {Var: Type} {signature: UserBodySignature Var} {variance: Var -> Sign}: SProp :=
{ ubsmethodv (method: scheme.(Method)) (contains: SCSetContains signature.(ubsmethods) method): UserMethodSignatureV (signature.(ubsmethod) method contains) variance;
}.
Arguments UserBodySignatureV {_} _ _.

Record UserInterfaceSignatureV {Var: Type} {signature: UserInterfaceSignature Var}: SProp :=
{ uisbodyv: UserBodySignatureV signature.(uisbody) signature.(uisvariance); }.
Arguments UserInterfaceSignatureV {_} _.

Record HierarchyV: SProp :=
{ hinterfacev (interface: scheme.(Interface)): UserInterfaceSignatureV (hierarchy.(hinterface) interface); }.



(* Part 3: Type-Consistency
 * Here we define type spaces, type-space consistency, and type-consistency.
 *)

(* Part 3.1: Type Spaces *)

Definition utfold {Var: Type} {T: Type} (fany: T) (finterface: forall interface: scheme.(Interface), (scheme.(IParameter) interface -> T) -> T) (fvar: Var -> T): UserType Var -> T
:= fix utfold (type: UserType Var): T
:= match type with
   | utvariable variable => fvar variable
   | utany => fany
   | utinterface interface arguments => finterface interface (fun parameter => utfold (arguments parameter))
   end.

(* A type space is defined as in Definition 7.1 of the paper, with UnReachable used as the name for the unnamed predicate. *)
Record TypeSpace: Type :=
{ SpaceType: Type;
  stany: SpaceType;
  stinterface (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> SpaceType): SpaceType;
  SubSpaceType: SpaceType -> SpaceType -> SProp;
  sstrefl (t: SpaceType): SubSpaceType t t;
  ssttrans (t t' t'': SpaceType): SubSpaceType t t' -> SubSpaceType t' t'' -> SubSpaceType t t'';
  sstvariance (interface: scheme.(Interface)) (arguments arguments': scheme.(IParameter) interface -> SpaceType): (forall parameter: scheme.(IParameter) interface, Signed SubSpaceType ((hierarchy.(hinterface) interface).(uisvariance) parameter) (arguments parameter) (arguments' parameter)) -> SubSpaceType (stinterface interface arguments) (stinterface interface arguments');
  sstinheritance (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> SpaceType): SubSpaceType (stinterface interface arguments) stany;
  UnReachable: SpaceType -> SProp;
  sstur (t t': SpaceType): SubSpaceType t t' -> UnReachable t' -> UnReachable t;
}.
Lemma sstvariance_eqS {Interface_SSet: SSet scheme.(Interface)} {space: TypeSpace} (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> space.(SpaceType)) (interface': scheme.(Interface)) (arguments': scheme.(IParameter) interface' -> space.(SpaceType)): forall e: eqS interface interface', (forall parameter: scheme.(IParameter) interface, Signed space.(SubSpaceType) ((hierarchy.(hinterface) interface).(uisvariance) parameter) (arguments parameter) (arguments' (convert e scheme.(IParameter) parameter))) -> space.(SubSpaceType) (space.(stinterface) interface arguments) (space.(stinterface) interface' arguments').
Proof.
  intro e.
  destruct (eqS_eq e); rewrite convert_id; clear e.
  apply space.(sstvariance).
Qed.
Lemma sstvariance_eqS' {Interface_SSet: SSet scheme.(Interface)} {space: TypeSpace} (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> space.(SpaceType)) (interface': scheme.(Interface)) (arguments': scheme.(IParameter) interface' -> space.(SpaceType)): forall e: eqS interface' interface, (forall parameter': scheme.(IParameter) interface', Signed space.(SubSpaceType) ((hierarchy.(hinterface) interface').(uisvariance) parameter') (arguments (convert e scheme.(IParameter) parameter')) (arguments' parameter')) -> space.(SubSpaceType) (space.(stinterface) interface arguments) (space.(stinterface) interface' arguments').
Proof.
  intro e.
  destruct (eqS_eq e); rewrite convert_id; clear e.
  apply space.(sstvariance).
Qed.
(* tsubst interprets a user type in a type space. *)
Definition tsubst {Var: Type} {space: TypeSpace}: (Var -> space.(SpaceType)) -> UserType Var -> space.(SpaceType)
:= utfold space.(stany) space.(stinterface).

Lemma tsubst_sub_tsubst (sign: Sign) (space: TypeSpace) {Var: Type} (variance: Var -> Sign) (type: UserType Var) (substitution substitution': Var -> space.(SpaceType)): UserVariance variance type sign -> (forall variable: Var, Signed space.(SubSpaceType) (variance variable) (substitution variable) (substitution' variable)) -> Signed space.(SubSpaceType) sign (tsubst substitution type) (tsubst substitution' type).
Proof.
  intros uv sub.
  induction uv; simpl.
  + apply sub.
  + apply signed_refl.
    apply sstrefl.
  + destruct sign; apply sstvariance; simpl in *; intro parameter.
    - apply signed_negate'.
      auto.
    - auto.
Qed.



(* Part 3.2: Non-User Signatures *)

(* A SpaceMethodSignature is a method signature in Figure 11 of the paper. *)
Record SpaceMethodSignature {space: TypeSpace} {Input: Type}: Type :=
{ smsinput (input: Input): space.(SpaceType);
  smsresult: space.(SpaceType);
}.
Arguments SpaceMethodSignature : clear implicits.
Definition mssubst {Var Input: Type} {space: TypeSpace} (substitution: Var -> space.(SpaceType)) (signature: UserMethodSignature Var Input): SpaceMethodSignature space Input :=
{| smsinput input := tsubst substitution (signature.(umsinput) input);
   smsresult := tsubst substitution signature.(umsresult);
|}.
(* A SpaceBodySignature is a body signature in Figure 11 of the paper. *)
Record SpaceBodySignature {space: TypeSpace}: Type :=
{ sbsmethods: SCSet scheme.(Method);
  sbsmethod (method: scheme.(Method)) (contains: SCSetContains sbsmethods method): SpaceMethodSignature space (scheme.(MInput) method);
}.
Arguments SpaceBodySignature : clear implicits.
Definition bssubst {Var: Type} {space: TypeSpace} (substitution: Var -> space.(SpaceType)) (signature: UserBodySignature Var): SpaceBodySignature space :=
{| sbsmethods := signature.(ubsmethods);
   sbsmethod method contains := mssubst substitution (signature.(ubsmethod) method contains);
|}.

(* These define subtyping between (space) method/body signatures, in line with Figure 11 of the paper. *)
Record SubSpaceMethodSignature {space: TypeSpace} {Input: Type} {signature signature': SpaceMethodSignature space Input}: SProp :=
{ ssmsinput (input: Input): space.(SubSpaceType) (signature'.(smsinput) input) (signature.(smsinput) input);
  ssmsresult: space.(SubSpaceType) signature.(smsresult) signature'.(smsresult);
}.
Arguments SubSpaceMethodSignature {_ _} _ _.
Record SubSpaceBodySignature {space: TypeSpace} {signature signature': SpaceBodySignature space}: SProp :=
{ ssbsmethods (method: scheme.(Method)): SCSetContains signature'.(sbsmethods) method -> SCSetContains signature.(sbsmethods) method;
  ssbsmethod (method: scheme.(Method)) (contains: SCSetContains signature'.(sbsmethods) method): SubSpaceMethodSignature (signature.(sbsmethod) method (ssbsmethods method contains)) (signature'.(sbsmethod) method contains);
}.
Arguments SubSpaceBodySignature {_} _ _.

Lemma ssmsrefl {space: TypeSpace} {Input: Type} (signature: SpaceMethodSignature space Input): SubSpaceMethodSignature signature signature.
Proof.
  constructor.
  + intro input.
    apply sstrefl.
  + apply sstrefl.
Qed.
Lemma ssmstrans {space: TypeSpace} {Input: Type} (signature signature' signature'': SpaceMethodSignature space Input): SubSpaceMethodSignature signature signature' -> SubSpaceMethodSignature signature' signature'' -> SubSpaceMethodSignature signature signature''.
Proof.
  intros sub sub'.
  constructor.
  + intro input.
    apply ssttrans with (signature'.(smsinput) input).
    - apply sub'.(ssmsinput).
    - apply sub.(ssmsinput).
  + apply ssttrans with signature'.(smsresult).
    - apply sub.(ssmsresult).
    - apply sub'.(ssmsresult).
Qed.
Lemma mssubst_sub_mssubst {Var Input: Type} (signature: UserMethodSignature Var Input) (variance: Var -> Sign) {space: TypeSpace} (substitution substitution': Var -> space.(SpaceType)): UserMethodSignatureV signature variance -> (forall variable: Var, Signed space.(SubSpaceType) (variance variable) (substitution variable) (substitution' variable)) -> SubSpaceMethodSignature (mssubst substitution signature) (mssubst substitution' signature).
Proof.
  intros svms sub.
  constructor; simpl.
  + intro input.
    eapply (tsubst_sub_tsubst negative); try eassumption.
    apply umsinputv.
    assumption.
  + eapply (tsubst_sub_tsubst positive); try eassumption.
    apply umsresultv.
    assumption.
Qed.

Lemma ssbstrans {space: TypeSpace} (signature signature' signature'': SpaceBodySignature space): SubSpaceBodySignature signature signature' -> SubSpaceBodySignature signature' signature'' -> SubSpaceBodySignature signature signature''.
Proof.
  intros sub sub'.
  refine {| ssbsmethods method contains := sub.(ssbsmethods) method (sub'.(ssbsmethods) method contains) |}.
  intros method contains.
  apply ssmstrans with (signature'.(sbsmethod) method (sub'.(ssbsmethods) method contains)).
  + apply sub.(ssbsmethod).
  + apply sub'.(ssbsmethod).
Qed.
Lemma bssubst_sub_bssubst {Var: Type} (signature: UserBodySignature Var) (variance: Var -> Sign) {space: TypeSpace} (substitution substitution': Var -> space.(SpaceType)): UserBodySignatureV signature variance -> (forall variable: Var, Signed space.(SubSpaceType) (variance variable) (substitution variable) (substitution' variable)) -> SubSpaceBodySignature (bssubst substitution signature) (bssubst substitution' signature).
Proof.
  intros vbody sub.
  refine {| ssbsmethods method (contains: SCSetContains (bssubst substitution' signature).(sbsmethods) method) := contains: SCSetContains (bssubst substitution signature).(sbsmethods) method |}.
  intros method contains.
  apply mssubst_sub_mssubst with variance; try assumption.
  apply vbody.(ubsmethodv).
Qed.



(* Part 3.3: Type-Checking *)

(* CheckMethod defines when a receiver has a method with a given (space) method signature, in line with Figure 11 of the paper. *)
Inductive CheckMethod {space: TypeSpace} {method: scheme.(Method)}: space.(SpaceType) -> SpaceMethodSignature space (scheme.(MInput) method) -> SProp
:= cmunreachable (treceiver: space.(SpaceType)) (signature: SpaceMethodSignature space (scheme.(MInput) method)): space.(UnReachable) treceiver -> CheckMethod treceiver signature
 | cminterface (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> space.(SpaceType)) (contains: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method): CheckMethod (space.(stinterface) interface arguments) (mssubst arguments ((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method contains)).
Arguments CheckMethod {_} _ _.
(* CheckExpression defines when an expression, within a given context, has a given (space) type.
 * It is the same as in Figure 11 of the paper, except that the separate judgement for body-signature compatibility with an interface has been directly incorprated.
 *)
Inductive CheckExpression {space: TypeSpace} | {Input: Sort} {context: SortElimination space.(SpaceType) Input}: Expression Input -> space.(SpaceType) -> SProp
:= cesub (expression: Expression Input) (t t': space.(SpaceType)): CheckExpression expression t -> space.(SubSpaceType) t t' -> CheckExpression expression t'
 | ceinput (input: SumSort Input): CheckExpression (einput input) (apply_elimination context input)
 | ceinvoke (ereceiver: Expression Input) (method: scheme.(Method)) (einputs: scheme.(MInput) method -> Expression Input) (treceiver: space.(SpaceType)) (signature: SpaceMethodSignature space (scheme.(MInput) method)): CheckMethod method treceiver signature -> CheckExpression ereceiver treceiver -> (forall input: scheme.(MInput) method, CheckExpression (einputs input) (signature.(smsinput) input)) -> CheckExpression (einvoke ereceiver method einputs) signature.(smsresult)
 | ceobject (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> Expression (cons (scheme.(MInput) method) Input)) (arguments: scheme.(IParameter) interface -> space.(SpaceType)) (signatures: forall method: scheme.(Method), SCSetContains methods method -> SpaceMethodSignature space (scheme.(MInput) method)): SubSpaceBodySignature {| sbsmethods := methods; sbsmethod := signatures |} (bssubst arguments (hierarchy.(hinterface) interface).(uisbody)) -> (forall method: scheme.(Method), forall contains: SCSetContains methods method, CheckExpression (context := pair_elimination (signatures method contains).(smsinput) context) (bodies method contains) (signatures method contains).(smsresult)) -> CheckExpression (eobject interface methods bodies) (space.(stinterface) interface arguments).
Arguments CheckExpression _ {_} _ _ _.

Lemma check_object
        (space: TypeSpace)
        {Input: Sort}
        (context: SortElimination space.(SpaceType) Input)
        (interface: scheme.(Interface))
        (methods: SCSet scheme.(Method))
        (bodies: forall method: scheme.(Method), SCSetContains methods method -> Expression (cons (scheme.(MInput) method) Input))
        (type: space.(SpaceType))
      : CheckExpression space context (eobject interface methods bodies) type
     -> existsTSS arguments: scheme.(IParameter) interface -> space.(SpaceType),
        space.(SubSpaceType) (space.(stinterface) interface arguments) type
      & existsTSS signatures: forall method: scheme.(Method), SCSetContains methods method -> SpaceMethodSignature space (scheme.(MInput) method),
        SubSpaceBodySignature {| sbsmethods := methods; sbsmethod := signatures |} (bssubst arguments (hierarchy.(hinterface) interface).(uisbody))
      & forall method: scheme.(Method), forall contains: SCSetContains methods method, CheckExpression space (pair_elimination (signatures method contains).(smsinput) context) (bodies method contains) (signatures method contains).(smsresult).
  intro check.
  remember (eobject interface methods bodies) as expression in check.
  induction check; try discriminate Heqexpression.
  + specialize (IHcheck bodies Heqexpression).
    destruct IHcheck as [ arguments ? ? ].
    exists arguments; try assumption.
    eapply ssttrans; eassumption.
  + inversion_hset Heqexpression.
    exists arguments; try apply sstrefl.
    exists signatures; try assumption.
Qed.

Lemma ceinvoke_sub {space: TypeSpace} {Input: Sort} {context: SortElimination space.(SpaceType) Input} (method: scheme.(Method)) (treceiver: space.(SpaceType)) (tinputs: scheme.(MInput) method -> space.(SpaceType)) (tresult: space.(SpaceType)) (ereceiver: Expression Input) (einputs: scheme.(MInput) method -> Expression Input): (existsTSS treceiver': space.(SpaceType), space.(SubSpaceType) treceiver treceiver' & existsTSS signature: SpaceMethodSignature space (scheme.(MInput) method), SubSpaceMethodSignature signature {| smsinput := tinputs; smsresult := tresult |} & CheckMethod method treceiver' signature) -> CheckExpression space context ereceiver treceiver -> (forall input: scheme.(MInput) method, CheckExpression space context (einputs input) (tinputs input)) -> CheckExpression space context (einvoke ereceiver method einputs) tresult.
Proof.
  intros [ treceiver' subr [ signature subs cm ] ] checkr checki.
  apply cesub with signature.(smsresult); try apply subs.(ssmsresult).
  apply ceinvoke with treceiver'; try assumption.
  + apply cesub with treceiver; assumption.
  + intro input.
    apply cesub with (tinputs input); try apply subs.(ssmsinput).
    apply checki.
Qed.

Definition CheckAExpression {space: TypeSpace} {Input: Sort} (context: SortElimination space.(SpaceType) Input) (expression: AExpression Input) (type: space.(SpaceType)): SProp
:= forall Input': Sort, forall incl: SumSort Input -> SumSort Input', forall context': SortElimination space.(SpaceType) Input', (forall input: SumSort Input, space.(SubSpaceType) (apply_elimination context' (incl input)) (apply_elimination context input)) -> CheckExpression space context' (expression Input' incl) type.
Lemma check_abstract {space: TypeSpace} {Input: Sort} (context: SortElimination space.(SpaceType) Input) (expression: Expression Input) (type: space.(SpaceType)): CheckExpression space context expression type -> CheckAExpression context (eabstract expression) type.
Proof.
  intro check.
  unfold CheckAExpression.
  induction check; simpl; intros Input' incl context' sub.
  + eapply cesub; eauto.
  + apply cesub with (apply_elimination context' (incl input)); try auto.
    apply ceinput.
  + eapply ceinvoke; eauto.
  + apply ceobject with signatures; try assumption.
    intros method contains.
    apply H.
    intros [ input | input ]; simpl.
    - apply sstrefl.
    - auto.
Qed.
Lemma check_asubstitute
        (space: TypeSpace)
        {Input: Sort}
        (context: SortElimination space.(SpaceType) Input)
        (expression: Expression Input)
        (type: space.(SpaceType))
        {Input': Sort}
        (context': SortElimination space.(SpaceType) Input')
        (substitution: SumSort Input -> AExpression Input')
        (type': space.(SpaceType))
      : CheckExpression space context expression type
     -> (forall input: SumSort Input, CheckAExpression context' (substitution input) (apply_elimination context input))
     -> space.(SubSpaceType) type type'
     -> CheckExpression space context' (aesubstitute expression substitution) type'.
Proof.
  intro check.
  intros check' sub.
  eapply cesub; try eassumption.
  clear type' sub.
  revert Input' context' substitution check'.
  induction check; intros Input' context' substitution' check'; simpl.
  + eapply cesub; eauto.
  + apply check'.
    intro.
    apply sstrefl.
  + eapply ceinvoke; eauto.
  + apply ceobject with signatures; try assumption.
    intros method contains'.
    apply H.
    intro input.
    unfold CheckAExpression.
    intros Input'' incl' context'' sub'.
    destruct input as [ input | input ]; simpl.
    - eapply cesub; try apply ceinput.
      apply sub'.
    - apply check'.
      auto.
Qed.
Lemma check_substitute
        (space: TypeSpace)
        {Input: Sort}
        (context: SortElimination space.(SpaceType) Input)
        (expression: Expression Input)
        (type: space.(SpaceType))
        {Input': Sort}
        (context': SortElimination space.(SpaceType) Input')
        (substitution: SumSort Input -> Expression Input')
        (type': space.(SpaceType))
      : CheckExpression space context expression type
     -> (forall input: SumSort Input, CheckExpression space context' (substitution input) (apply_elimination context input))
     -> space.(SubSpaceType) type type'
     -> CheckExpression space context' (esubstitute expression substitution) type'.
Proof.
  intros check check'.
  apply check_asubstitute with context; try assumption.
  intro input.
  apply check_abstract.
  auto.
Qed.



(* Part 3.4: Type-Space Consistency *)

(* This defines type-space consistency in line with Figure 12 of the paper (though with the "or" split into two requirements). *)
Record ConsistentTypeSpace `{SSet scheme.(Interface)} {space: TypeSpace}: SProp :=
{ ctsinterface (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> space.(SpaceType)) (interface': scheme.(Interface)) (arguments': scheme.(IParameter) interface' -> space.(SpaceType)): space.(SubSpaceType) (space.(stinterface) interface arguments) (space.(stinterface) interface' arguments') -> existsSS e: eqS interface interface', forall parameter: scheme.(IParameter) interface, Signed space.(SubSpaceType) ((hierarchy.(hinterface) interface).(uisvariance) parameter) (arguments parameter) (arguments' (convert e scheme.(IParameter) parameter));
  ctsanyunreachable: space.(UnReachable) space.(stany) -> FalseS;
  ctsanyinterface (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> space.(SpaceType)): space.(SubSpaceType) space.(stany) (space.(stinterface) interface arguments) -> FalseS;
  ctsinterfaceunreachable (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> space.(SpaceType)): space.(UnReachable) (space.(stinterface) interface arguments) -> FalseS;
}.
Arguments ConsistentTypeSpace {_} _.



(* Part 3.5: The User Type Space
 * While not actually used anywhere else in our proof, Theorem 7.2 of the paper states that closed user types form a consistent type space.
 * The following define that type space and prove the required properties.
 *)

(* User subtyping is defined as in Figure 10 of the paper. *)
Inductive SubUserType {Var: Type}: UserType Var -> UserType Var -> SProp
:= sutvariable (variable: Var): SubUserType (utvariable variable) (utvariable variable)
 | sutany: SubUserType utany utany
 | sutvariance (interface: scheme.(Interface)) (arguments arguments': scheme.(IParameter) interface -> UserType Var): (forall parameter: scheme.(IParameter) interface, ISigned SubUserType ((hierarchy.(hinterface) interface).(uisvariance) parameter) (arguments parameter) (arguments' parameter)) -> SubUserType (utinterface interface arguments) (utinterface interface arguments')
 | sutinheritance (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> UserType Var): SubUserType (utinterface interface arguments) utany.
Lemma sutrefl {Var: Type}: forall type: UserType Var, SubUserType type type.
Proof.
  fix sutrefl 1.
  intro type.
  destruct type.
  + apply sutvariable.
  + apply sutany.
  + apply sutvariance.
    intro parameter.
    apply signed_isigned.
    apply signed_refl.
    apply sutrefl.
Qed.
Lemma suttrans {Interface_SSet: SSet scheme.(Interface)} {Var: Type}: forall type type' type'': UserType Var, SubUserType type type' -> SubUserType type' type'' -> SubUserType type type''.
Proof.
  fix suttrans 2.
  intros type type' type'' sub sub'.
  destruct type'; inversion_hset sub; inversion_hset sub'.
  + apply sutvariable.
  + apply sutany.
  + apply sutinheritance.
  + clear arguments0.
    rename arguments' into arguments''.
    rename arguments into arguments'.
    rename arguments1 into arguments.
    rename H1 into sub.
    rename H3 into sub'.
    apply sutvariance.
    intro parameter.
    specialize (sub parameter).
    specialize (sub' parameter).
    apply isigned_signed in sub.
    apply isigned_signed in sub'.
    apply signed_isigned.
    destruct ((hierarchy.(hinterface) interface).(uisvariance) parameter); eapply suttrans; eassumption.
  + apply sutinheritance.
Qed.
Inductive UnReachableUserType: UserType Empty -> SProp
:=.
Lemma sutur (type type': UserType Empty): SubUserType type type' -> UnReachableUserType type' -> UnReachableUserType type.
Proof.
  intros _ [ ].
Qed.
Definition UserTypeSpace {Interface_SSet: SSet scheme.(Interface)}: TypeSpace :=
{| SpaceType := UserType Empty;
   stany := utany;
   stinterface := utinterface;
   SubSpaceType := SubUserType;
   sstrefl := sutrefl;
   ssttrans := suttrans;
   sstvariance interface arguments arguments' sub := sutvariance interface arguments arguments' (fun parameter => signed_isigned (sub parameter));
   sstinheritance := sutinheritance;
   UnReachable := UnReachableUserType;
   sstur := sutur;
|}.
Lemma usertypespace_consistent {Interface_SSet: SSet scheme.(Interface)}: ConsistentTypeSpace UserTypeSpace.
Proof.
  constructor; cbv.
  + intros interface arguments interface' arguments' sub.
    inversion_hset sub.
    exists (eqS_refl _).
    rewrite convert_id.
    intro parameter.
    apply isigned_signed.
    auto.
  + intros [ ].
  + intros interface arguments sub.
    inversion_hset sub.
  + intros _ _ [ ].
Qed.

(* The following prints only scheme: Scheme and hierarchy: Hierarchy. *)
Print Assumptions usertypespace_consistent.



(* Part 3.6: Type-Consistency *)

(* Program validity, i.e. type-consistency, is defined in line with Figure 13 of the paper (though with fewer intermediate judgements, and with type-validity automatically guaranteed due to the use of Schemes). *)
Record ProgramV `{SSet scheme.(Interface)} {program: Program}: SProp :=
{ phierarchyv: HierarchyV;
  pexpressionv: existsTSS space: TypeSpace, ConsistentTypeSpace space & CheckExpression space nil_elimination program.(pexpression) (tsubst emptye program.(ptype));
}.
Arguments ProgramV {_} _.



(* Part 4: Proving Safety of Type-Consistency
 * It is worth noting that the following proofs are relatively small, illustrating that type-consistency provides a simple way to ensure safety.
 *)

(* This is the first intermediate fact used in the proof of safey in the paper.
 * It states that no value can have an unreachable type.
 *)
Lemma no_value_unreachable
        {Interface_SSet: SSet scheme.(Interface)}
        (space: TypeSpace)
        {Input: Sort}
        (context: SortElimination space.(SpaceType) Input)
        (expression: Expression Input)
        (type: space.(SpaceType))
      : ConsistentTypeSpace space
     -> CheckExpression space context expression type
     -> Value expression
     -> space.(UnReachable) type
     -> FalseS.
Proof.
  intros consistent check value unreachable.
  destruct value.
  apply check_object in check.
  destruct check as [ arguments sub _ ].
  eapply ctsinterfaceunreachable; try eassumption.
  eapply sstur; eassumption.
Qed.
(* This is the second intermediate fact used in the proof of safey in the paper.
 * It states that an object can only have an interface type if its body signature is compatible with the body signature of the interface type.
 *)
Lemma check_object_interface
        {Interface_SSet: SSet scheme.(Interface)}
        (space: TypeSpace)
        {Input: Sort}
        (context: SortElimination space.(SpaceType) Input)
        (interface: scheme.(Interface))
        (methods: SCSet scheme.(Method))
        (bodies: forall method: scheme.(Method), SCSetContains methods method -> Expression (cons (scheme.(MInput) method) Input))
        (interface': scheme.(Interface))
        (arguments': scheme.(IParameter) interface' -> space.(SpaceType))
      : HierarchyV
     -> ConsistentTypeSpace space
     -> CheckExpression space context (eobject interface methods bodies) (space.(stinterface) interface' arguments')
     -> existsTSS signatures: forall method: scheme.(Method), SCSetContains methods method -> SpaceMethodSignature space (scheme.(MInput) method),
        SubSpaceBodySignature {| sbsmethods := methods; sbsmethod := signatures |} (bssubst arguments' (hierarchy.(hinterface) interface').(uisbody))
      & forall method: scheme.(Method), forall contains: SCSetContains methods method, CheckExpression space (pair_elimination (signatures method contains).(smsinput) context) (bodies method contains) (signatures method contains).(smsresult).
Proof.
  intros vhierarchy consistent check.
  apply check_object in check.
  destruct check as [ arguments sub [ signatures bsub check ] ].
  exists signatures; try assumption.
  clear check.
  apply ctsinterface in sub; try assumption.
  destruct sub as [ e sub ].
  destruct (eqS_eq e).
  rewrite convert_id in *.
  clear e.
  eapply ssbstrans; try eassumption.
  eapply bssubst_sub_bssubst; try eassumption.
  apply vhierarchy.(hinterfacev).
Qed.

(* This ensures progress for typed closed expressions. *)
Lemma progress
        {Interface_SSet: SSet scheme.(Interface)}
        (space: TypeSpace)
        (expression: Expression nil)
        (type: space.(SpaceType))
      : HierarchyV
     -> ConsistentTypeSpace space
     -> CheckExpression space nil_elimination expression type
     -> OrS (Value expression)
            (existsTS expression': Expression nil, StepsTo expression expression').
Proof.
  intros svhierarchy consistent.
  revert expression.
  generalize (@nil_elimination space.(SpaceType)).
  generalize (@nil_elimination False).
  generalize (@nil Type).
  intros Input noinput context expression check.
  induction check.
  + specialize (IHcheck noinput).
    assumption.
  + destruct (apply_elimination noinput input).
  + specialize (IHcheck noinput).
    right.
    destruct IHcheck as [ value | [ expression' step ] ].
    - destruct c as [ | interface' arguments' contains' ]; [ edestruct no_value_unreachable; eassumption | ].
      destruct value as [ interface methods ].
      apply check_object_interface in check; try assumption.
      destruct check as [ signatures bsub _ ].
      eexists.
      eapply step_invoke with (contains := bsub.(ssbsmethods) method contains').
    - eexists.
      apply step_receiver.
      eassumption.
  + left.
    constructor.
Qed.
(* This ensures preservation for typed closed expressions. *)
Lemma preservation
        {Interface_SSet: SSet scheme.(Interface)}
        (space: TypeSpace)
        (expression expression': Expression nil)
        (type: space.(SpaceType))
      : HierarchyV
     -> ConsistentTypeSpace space
     -> CheckExpression space nil_elimination expression type
     -> StepsTo expression expression'
     -> CheckExpression space nil_elimination expression' type.
Proof.
  intros vhierarchy consistent check step.
  revert type check.
  induction step; intros type check.
  + remember (einvoke receiver method arguments) as expression.
    induction check; try discriminate Heqexpression.
    - eapply cesub; eauto.
    - inversion_hset Heqexpression.
      eapply ceinvoke; try eassumption.
      apply IHstep.
      assumption.
  + remember (einvoke (eobject interface methods bodies) method arguments) as expression.
    induction check; try discriminate Heqexpression.
    - eapply cesub; eauto.
    - inversion_hset Heqexpression.
      destruct c as [ | interface' arguments' contains' ]; [ edestruct no_value_unreachable; try apply vobject; eassumption | ].
      apply check_object_interface in check; try assumption.
      destruct check as [ signatures bsub check ].
      merge (bsub.(ssbsmethods) method contains') contains.
      eapply check_substitute; try eauto.
      * intros [ input | input ]; simpl; try apply ceinput.
        eapply cesub; try eauto.
        apply ssmsinput.
        apply bsub.(ssbsmethod).
      * apply ssmsresult.
        apply bsub.(ssbsmethod).
Qed.
(* This is Theorem 7.3 of the paper. *)
Theorem safety {Interface_SSet: SSet scheme.(Interface)}
               (space: TypeSpace)
               (expression: Expression nil)
               (type: space.(SpaceType))
             : HierarchyV
            -> ConsistentTypeSpace space
            -> CheckExpression space nil_elimination expression type
            -> AndS (OrS (Value expression) (existsTS expression': Expression nil, StepsTo expression expression'))
                    (forall expression': Expression nil, StepsTo expression expression' -> CheckExpression space nil_elimination expression' type).
Proof.
  intros consistent check.
  split.
  + eapply progress; eassumption.
  + intro.
    eapply preservation; eassumption.
Qed.

(* The following prints only scheme: Scheme and hierarchy: Hierarchy. *)
Print Assumptions safety.



(* Part 5: Graphical Cores
 * Here we define graphical cores, histories (which generalize configurations), and constraint-derivation.
 *)

(* Part 5.1: Graphical Cores
 * Unlike in Definition 8.1 of the paper, here we define graphical cores recursively.
 * This makes them much more expressive here than in the paper.
 * For example, suppose method invocation did not require its argument to type-check if the receiver can be given an unreachable type.
 * Then here we could express a graphical core where the events for the label-listener for that invocation dynamically add the graphical core representing the argument to the invocation.
 * This essentially lazily adds constraints, and is only safe when the arguments are themselves evaluated lazily, illustrating how our algorithm can easily more directly connect to the operational semantics of the language at hand.
 * Because many of the constructions and proofs pertaining to graphical cores do not require finiteness, we leave that as a separate property of graphical cores and here define them coinductively.
 * As a consequence, rather than using events, we instead use a GCLKeyedS predicate that indicates which interfaces a label-listener can be resolved to, with gclaction specifying the graphical core representing the action to be fired should that resolution occur.
 *)
CoInductive GraphicalCore {Transitive: Sort}: Type :=
{ GCAbstract: Type;
  GCNode: Type;
  GCListener: Type;
  GCConstraint: Type;
  gcninterface (node: GCNode): scheme.(Interface);
  gcnargument (node: GCNode) (parameter: scheme.(IParameter) (gcninterface node)): SumSort (cons Unit (cons GCNode (cons GCAbstract Transitive)));
  gcclower (constraint: GCConstraint): SumSort (cons Unit (cons GCNode (cons GCAbstract Transitive)));
  gccupper (constraint: GCConstraint): SumSort (cons GCListener (cons Unit (cons GCNode (cons GCAbstract Transitive))));
  GCLKeyedS (listener: GCListener) (interface: scheme.(Interface)): SProp;
  gclaction (listener: GCListener) (interface: scheme.(Interface)) (keyed: GCLKeyedS listener interface): GraphicalCore (Transitive := cons (scheme.(IParameter) interface) (cons GCAbstract Transitive));
}.
Arguments GraphicalCore : clear implicits.

Definition gcmap: forall {Transitive Transitive': Sort} (tmap: SortMorphism Transitive Transitive'), GraphicalCore Transitive -> GraphicalCore Transitive'
:= cofix gcmap {Transitive Transitive': Sort} (vmap: SortMorphism Transitive Transitive') (core: GraphicalCore Transitive): GraphicalCore Transitive' :=
{| GCAbstract := core.(GCAbstract);
   GCNode := core.(GCNode);
   GCListener := core.(GCListener);
   GCConstraint := core.(GCConstraint);
   gcninterface := core.(gcninterface);
   gcnargument node parameter := apply_morphism (consid_morphism Unit (consid_morphism core.(GCNode) (consid_morphism core.(GCAbstract) vmap))) (core.(gcnargument) node parameter);
   gcclower constraint := apply_morphism (consid_morphism Unit (consid_morphism core.(GCNode) (consid_morphism core.(GCAbstract) vmap))) (core.(gcclower) constraint);
   gccupper constraint := apply_morphism (consid_morphism core.(GCListener) (consid_morphism Unit (consid_morphism core.(GCNode) (consid_morphism core.(GCAbstract) vmap)))) (core.(gccupper) constraint);
   GCLKeyedS := core.(GCLKeyedS);
   gclaction listener interface keyed := gcmap (consid_morphism (scheme.(IParameter) interface) (consid_morphism core.(GCAbstract) vmap)) (core.(gclaction) listener interface keyed);
|}.



(* Part 5.2: Nested Components and Constraints
 * Because graphical cores are recursive, many components can occur deeply nested within a graphical core.
 * The following collect those nested components, similar to how we flatten the non-recursive graphical core in the paper.
 *)

(* GCNTransitive represent all the components that represent unknowns, and which can be used as the middle component for deriving constraints transitively. *)
Inductive GCNTransitive | {Transitive: Sort} {core: GraphicalCore Transitive}: Type
:= gcntabstract (abstract: core.(GCAbstract))
 | gcntargument (listener: core.(GCListener)) (interface: scheme.(Interface)) (keyed: core.(GCLKeyedS) listener interface) (parameter: scheme.(IParameter) interface)
 | gcntnested (listener: core.(GCListener)) (interface: scheme.(Interface)) (keyed: core.(GCLKeyedS) listener interface) (transitive: GCNTransitive (core := core.(gclaction) listener interface keyed)).
Arguments GCNTransitive {_} _.

Inductive GCNNode | {Transitive: Sort} {core: GraphicalCore Transitive}: Type
:= gcnnnode (node: core.(GCNode))
 | gcnnnested (listener: core.(GCListener)) (interface: scheme.(Interface)) (keyed: core.(GCLKeyedS) listener interface) (node: GCNNode (core := core.(gclaction) listener interface keyed)).
Arguments GCNNode {_} _.
Definition gcnninterface: forall {Transitive: Sort} {core: GraphicalCore Transitive}, GCNNode core -> scheme.(Interface)
:= fix gcnninterface {Transitive: Sort} {core: GraphicalCore Transitive} (node: GCNNode core): scheme.(Interface)
:= match node with
   | gcnnnode node => core.(gcninterface) node
   | gcnnnested _ _ _ node => gcnninterface node
   end.
Definition gcnnargument: forall {Transitive: Sort} {core: GraphicalCore Transitive} (node: GCNNode core), scheme.(IParameter) (gcnninterface node) -> SumSort (cons Unit (cons (GCNNode core) (cons (GCNTransitive core) Transitive)))
:= fix gcnnargument {Transitive: Sort} {core: GraphicalCore Transitive} (node: GCNNode core): scheme.(IParameter) (gcnninterface node) -> SumSort (cons Unit (cons (GCNNode core) (cons (GCNTransitive core) Transitive)))
:= match node as node return scheme.(IParameter) (gcnninterface node) -> SumSort (cons Unit (cons (GCNNode core) (cons (GCNTransitive core) Transitive))) with
   | gcnnnode node => fun parameter => apply_morphism (consid_morphism Unit (cons_morphism gcnnnode (cons_morphism gcntabstract id_morphism))) (core.(gcnargument) node parameter)
   | gcnnnested listener interface keyed node => fun parameter => apply_morphism (consid_morphism Unit (cons_morphism (gcnnnested listener interface keyed) (pair_morphism (select_head (gcntnested listener interface keyed)) (pair_morphism (select_head (gcntargument listener interface keyed)) (cons_morphism gcntabstract id_morphism))))) (gcnnargument node parameter)
   end.

Inductive GCNListener | {Transitive: Sort} {core: GraphicalCore Transitive}: Type
:= gcnllistener (listener: core.(GCListener))
 | gcnlnested (listener: core.(GCListener)) (interface: scheme.(Interface)) (keyed: core.(GCLKeyedS) listener interface) (listener': GCNListener (core := core.(gclaction) listener interface keyed)).
Arguments GCNListener {_} _.
Definition GCNLKeyedS: forall {Transitive: Sort} {core: GraphicalCore Transitive} (listener: GCNListener core), scheme.(Interface) -> SProp
:= fix GCNLKeyedS {Transitive: Sort} {core: GraphicalCore Transitive} (listener: GCNListener core): scheme.(Interface) -> SProp
:= match listener with
   | gcnllistener listener => core.(GCLKeyedS) listener
   | gcnlnested listener interface keyed listener' => GCNLKeyedS listener'
   end.
Definition gcntlargument: forall {Transitive: Sort} {core: GraphicalCore Transitive} (listener: GCNListener core) (interface: scheme.(Interface)), GCNLKeyedS listener interface -> scheme.(IParameter) interface -> GCNTransitive core
:= fix gcntlargument {Transitive: Sort} {core: GraphicalCore Transitive} (listener: GCNListener core): forall interface: scheme.(Interface), GCNLKeyedS listener interface -> scheme.(IParameter) interface -> GCNTransitive core
:= match listener as listener return forall interface: scheme.(Interface), GCNLKeyedS listener interface -> scheme.(IParameter) interface -> GCNTransitive core with
   | gcnllistener listener => gcntargument listener
   | gcnlnested listener interface keyed listener' => fun interface' keyed' parameter' => gcntnested listener interface keyed (gcntlargument listener' interface' keyed' parameter')
   end.

(* The concrete components of a graphical core are those that represent (in some configuration) a (shallowly) known type. *)
Inductive GCConcrete {Transitive: Sort} {core: GraphicalCore Transitive}: Type
:= gcclistener (listener: GCNListener core)
 | gccnode (node: GCNNode core)
 | gccany.
Arguments GCConcrete {_} _.
(* The transitive components of a graphical core are those that represent the unknown types. *)
Inductive GCTransitive {Transitive: Sort} {core: GraphicalCore Transitive}: Type
:= gctntransitive (transitive: GCNTransitive core)
 | gcttransitive (transitive: SumSort Transitive).
Arguments GCTransitive {_} _.
(* The atoms of a graphical core are the union of its concrete and transitive components. *)
Inductive GCAtom {Transitive: Sort} {core: GraphicalCore Transitive}: Type
:= gcaconcrete (concrete: GCConcrete core)
 | gcatransitive (transitive: GCTransitive core).
Arguments GCAtom {_} _.
Definition gcatomize {Transitive: Sort} (core: GraphicalCore Transitive): SortElimination (GCAtom core) (cons Unit (cons (GCNNode core) (cons (GCNTransitive core) Transitive)))
:= pair_elimination (fun _ => gcaconcrete gccany) (pair_elimination (compose gccnode gcaconcrete) (pair_elimination (compose gctntransitive gcatransitive) (compose_elimination (eliminate_sum gcttransitive) gcatransitive))).
Definition gcatomizel {Transitive: Sort} (core: GraphicalCore Transitive): SortElimination (GCAtom core) (cons (GCNListener core) (cons Unit (cons (GCNNode core) (cons (GCNTransitive core) Transitive))))
:= pair_elimination (compose gcclistener gcaconcrete) (gcatomize core).

Inductive GCNConstraint | {Transitive: Sort} {core: GraphicalCore Transitive}: Type
:= gcncconstraint (constraint: core.(GCConstraint))
 | gcncnested (listener: core.(GCListener)) (interface: scheme.(Interface)) (keyed: core.(GCLKeyedS) listener interface) (constraint: GCNConstraint (core := core.(gclaction) listener interface keyed)).
Arguments GCNConstraint {_} _.
Definition gcnclower: forall {Transitive: Sort} {core: GraphicalCore Transitive}, GCNConstraint core -> SumSort (cons Unit (cons (GCNNode core) (cons (GCNTransitive core) Transitive)))
:= fix gcnclower {Transitive: Sort} {core: GraphicalCore Transitive} (constraint: GCNConstraint core): SumSort (cons Unit (cons (GCNNode core) (cons (GCNTransitive core) Transitive)))
:= match constraint as constraint return SumSort (cons Unit (cons (GCNNode core) (cons (GCNTransitive core) Transitive))) with
   | gcncconstraint constraint => apply_morphism (consid_morphism Unit (cons_morphism gcnnnode (cons_morphism gcntabstract id_morphism))) (core.(gcclower) constraint)
   | gcncnested listener interface keyed constraint => apply_morphism (consid_morphism Unit (cons_morphism (gcnnnested listener interface keyed) (pair_morphism (select_head (gcntnested listener interface keyed)) (pair_morphism (select_head (gcntargument listener interface keyed)) (cons_morphism gcntabstract id_morphism))))) (gcnclower constraint)
   end.
Definition gcncupper: forall {Transitive: Sort} {core: GraphicalCore Transitive}, GCNConstraint core -> SumSort (cons (GCNListener core) (cons Unit (cons (GCNNode core) (cons (GCNTransitive core) Transitive))))
:= fix gcncupper {Transitive: Sort} {core: GraphicalCore Transitive} (constraint: GCNConstraint core): SumSort (cons (GCNListener core) (cons Unit (cons (GCNNode core) (cons (GCNTransitive core) Transitive))))
:= match constraint as constraint return SumSort (cons (GCNListener core) (cons Unit (cons (GCNNode core) (cons (GCNTransitive core) Transitive)))) with
   | gcncconstraint constraint => apply_morphism (cons_morphism gcnllistener (consid_morphism Unit (cons_morphism gcnnnode (cons_morphism gcntabstract id_morphism)))) (core.(gccupper) constraint)
   | gcncnested listener interface keyed constraint => apply_morphism (cons_morphism (gcnlnested listener interface keyed) (consid_morphism Unit (cons_morphism (gcnnnested listener interface keyed) (pair_morphism (select_head (gcntnested listener interface keyed)) (pair_morphism (select_head (gcntargument listener interface keyed)) (cons_morphism gcntabstract id_morphism)))))) (gcncupper constraint)
   end.
Definition gcaclower {Transitive: Sort} {core: GraphicalCore Transitive} (constraint: GCNConstraint core): GCAtom core
:= apply_elimination (gcatomize core) (gcnclower constraint).
Definition gcacupper {Transitive: Sort} {core: GraphicalCore Transitive} (constraint: GCNConstraint core): GCAtom core
:= apply_elimination (gcatomizel core) (gcncupper constraint).



(* Part 5.3: Histories
 * A history is a propositional generalization of a configuration, thereby generalizing Definition 8.2 of the paper.
 * Its GCHKeyedS predicate indicates which label-listeners are currently resolved as which interfaces.
 * Its GCHUnResolvedS predicate indicates which label-listeners are currently unresolved.
 * This formalization makes it easier to extend this proof to inheritance, wherein a label-listener can be initially resolved to a subinterface and later relaxed to a superinterface as more lower bounds are derived, with the history indicating all the resolutions it ever had.
 * Similarly, a history is more amenable to the circumstance where the algorithm has not yet determined a required resolution for a label-listener but also has not determined the label-listener can be fixed as unresolved.
 * Histories are coinductively defined in order to recursively specify the histories of the nested graphical cores.
 *)
CoInductive GCHistory {Transitive: Sort} {core: GraphicalCore Transitive}: Type :=
{ GCHKeyedS (listener: GCListener core) (interface: scheme.(Interface)): SProp;
  GCHUnResolvedS (listener: GCListener core): SProp;
  gchkeyed {listener: GCListener core} {interface: scheme.(Interface)} (keyed: GCHKeyedS listener interface): core.(GCLKeyedS) listener interface;
  gchaction (listener: GCListener core) (interface: scheme.(Interface)) (keyed: GCHKeyedS listener interface): GCHistory (core := core.(gclaction) listener interface (gchkeyed keyed));
}.
Arguments GCHistory {_} _.

(* GCNHKeyedS indicates which nested label-listeners are resovled to which interfaces by a given history. *)
Definition GCNHKeyedS: forall {Transitive: Sort} {core: GraphicalCore Transitive}, GCHistory core -> GCNListener core -> scheme.(Interface) -> SProp
:= fix GCNHKeyedS {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (listener: GCNListener core): scheme.(Interface) -> SProp
:= match listener with
   | gcnllistener listener => history.(GCHKeyedS) listener
   | gcnlnested listener interface _ listener' => fun interface' => existsSS hkeyed: history.(GCHKeyedS) listener interface, GCNHKeyedS (history.(gchaction) listener interface hkeyed) listener' interface'
   end.
Definition gcnhkeyed: forall {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {listener: GCNListener core} {interface: scheme.(Interface)}, GCNHKeyedS history listener interface -> GCNLKeyedS listener interface
:= fix gcnhkeyed {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {listener: GCNListener core} {struct listener}: forall interface: scheme.(Interface), GCNHKeyedS history listener interface -> GCNLKeyedS listener interface
:= match listener as listener return forall {interface: scheme.(Interface)}, GCNHKeyedS history listener interface -> GCNLKeyedS listener interface with
   | gcnllistener listener => fun _ => history.(gchkeyed)
   | gcnlnested listener interface _ listener' => fun interface' hkeyed' => gcnhkeyed interface' hkeyed'.(proj2_exSS)
   end.
(* GCNHKeyedS indicates which nested label-listeners are unresovled according to a given history. *)
Definition GCNHUnResolvedS: forall {Transitive: Sort} {core: GraphicalCore Transitive}, GCHistory core -> GCNListener core -> SProp
:= fix GCNHUnResolvedS {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (listener: GCNListener core): SProp
:= match listener with
   | gcnllistener listener => history.(GCHUnResolvedS) listener
   | gcnlnested listener interface _ listener' => existsSS hkeyed: history.(GCHKeyedS) listener interface, GCNHUnResolvedS (history.(gchaction) listener interface hkeyed) listener'
   end.

Definition gcmap_history: forall {Transitive Transitive': Sort} (morphism: SortMorphism Transitive Transitive') {core: GraphicalCore Transitive} (history: GCHistory core), GCHistory (gcmap morphism core)
:= cofix gcmap_history {Transitive Transitive': Sort} (morphism: SortMorphism Transitive Transitive') {core: GraphicalCore Transitive} (history: GCHistory core): GCHistory (gcmap morphism core)
:= Build_GCHistory Transitive' (gcmap morphism core)
                   history.(GCHKeyedS)
                   history.(GCHUnResolvedS)
                   (fun listener interface => history.(gchkeyed))
                   (fun listener interface hkeyed => gcmap_history _ (history.(gchaction) listener interface hkeyed)).



(* Part 5.4: Activation
 * Because coinductive graphical cores represent dynamically generated components and constraints, we have a notion of when a given component or constraint is "activated" within the current history.
 * These activated components and constraints represent the subset of potentional components and constraints that have actually been generated at the current point of execution.
 * While the set of potential components and constraints can be infinite, this incorporation of dynamism is used to keep the activated subset finite.
 * This is a generalization of the notion of activation used in Figure 14.
 *)
Definition GCNCActivatedS: forall {Transitive: Sort} {core: GraphicalCore Transitive}, GCHistory core -> GCNConstraint core -> SProp
:= fix GCNCActivatedS {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (constraint: GCNConstraint core): SProp
:= match constraint with
   | gcncconstraint _ => TrueS
   | gcncnested listener interface _ constraint => existsSS hkeyed: history.(GCHKeyedS) listener interface, GCNCActivatedS (history.(gchaction) listener interface hkeyed) constraint
   end.

Definition GCNTActivatedS: forall {Transitive: Sort} {core: GraphicalCore Transitive}, GCHistory core -> GCNTransitive core -> SProp
:= fix GCNTActivatedS {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (transitive: GCNTransitive core): SProp
:= match transitive with
   | gcntabstract _ => TrueS
   | gcntargument listener interface _ _ => history.(GCHKeyedS) listener interface
   | gcntnested listener interface _ transitive => existsSS hkeyed: history.(GCHKeyedS) listener interface, GCNTActivatedS (history.(gchaction) listener interface hkeyed) transitive
   end.
Definition GCNLActivatedS: forall {Transitive: Sort} {core: GraphicalCore Transitive}, GCHistory core -> GCNListener core -> SProp
:= fix GCNLActivatedS {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (listener: GCNListener core): SProp
:= match listener with
   | gcnllistener _ => TrueS
   | gcnlnested listener interface _ listener' => existsSS hkeyed: history.(GCHKeyedS) listener interface, GCNLActivatedS (history.(gchaction) listener interface hkeyed) listener'
   end.
Definition GCNNActivatedS: forall {Transitive: Sort} {core: GraphicalCore Transitive}, GCHistory core -> GCNNode core -> SProp
:= fix GCNNActivatedS {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (node: GCNNode core): SProp
:= match node with
   | gcnnnode _ => TrueS
   | gcnnnested listener interface _ node => existsSS hkeyed: history.(GCHKeyedS) listener interface, GCNNActivatedS (history.(gchaction) listener interface hkeyed) node
   end.

Definition GCCActivatedS {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (concrete: GCConcrete core): SProp
:= match concrete with
   | gcclistener listener => GCNLActivatedS history listener
   | gccnode node => GCNNActivatedS history node
   | gccany => TrueS
   end.
Definition GCTActivatedS {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (transitive: GCTransitive core): SProp
:= match transitive with
   | gctntransitive transitive => GCNTActivatedS history transitive
   | gcttransitive _ => TrueS
   end.
Definition GCAActivatedS {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (atom: GCAtom core): SProp
:= match atom with
   | gcaconcrete concrete => GCCActivatedS history concrete
   | gcatransitive transitive => GCTActivatedS history transitive
   end.

Lemma gcnlactivatedS {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {listener: GCNListener core} {interface: scheme.(Interface)} (hkeyed: GCNHKeyedS history listener interface): GCNLActivatedS history listener.
Proof.
  induction listener; simpl in *.
  + constructor.
  + destruct hkeyed as [ hkeyed hkeyed' ].
    exists hkeyed.
    apply IHlistener.
    assumption.
Qed.
Lemma gcnlactivatedS' {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {listener: GCNListener core} (ur: GCNHUnResolvedS history listener): GCNLActivatedS history listener.
Proof.
  induction listener; simpl in *.
  + constructor.
  + destruct ur as [ hkeyed ur ].
    exists hkeyed.
    apply IHlistener.
    assumption.
Qed.

Lemma gcnnargument_activated {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} (node: GCNNode core) (parameter: scheme.(IParameter) (gcnninterface node)): GCNNActivatedS history node -> GCAActivatedS history (apply_elimination (gcatomize core) (gcnnargument node parameter)).
Proof.
  intro activated.
  induction node; simpl in *.
  + destruct (core.(gcnargument) node parameter) as [ [] | [ node' | [ transitive' | transitive' ] ] ]; simpl; try constructor.
    rewrite apply_extend_morphism.
    rewrite apply_extend_morphism.
    rewrite apply_extend_morphism.
    simpl.
    rewrite apply_compose_elimination.
    rewrite apply_eliminate_sum.
    constructor.
  + destruct activated as [ hkeyed activated ].
    merge (history.(gchkeyed) hkeyed) keyed.
    specialize (IHnode (history.(gchaction) listener interface hkeyed) parameter activated).
    destruct (gcnnargument node parameter) as [ [] | [ node' | [ transitive' | [ parameter' | [ abstract' | transitive' ] ] ] ] ]; simpl in *.
    - constructor.
    - exists hkeyed.
      assumption.
    - exists hkeyed.
      assumption.
    - assumption.
    - constructor.
    - rewrite apply_extend_morphism.
      rewrite apply_extend_morphism.
      rewrite apply_extend_morphism.
      simpl.
      rewrite apply_compose_elimination.
      rewrite apply_eliminate_sum.
      constructor.
Qed.
Lemma gcntlargument_activated {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} (listener: GCNListener core) (interface: scheme.(Interface)) (hkeyed: GCNHKeyedS history listener interface) (parameter: scheme.(IParameter) interface): GCNLActivatedS history listener -> GCNTActivatedS history (gcntlargument listener interface (gcnhkeyed hkeyed) parameter).
Proof.
  intro activated.
  induction listener; simpl in *.
  + assumption.
  + destruct activated as [ hkeyed' activated ].
    exists hkeyed'.
    apply IHlistener.
    assumption.
Qed.
Lemma constraint_activated {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {constraint: GCNConstraint core}: GCNCActivatedS history constraint -> AndS (GCAActivatedS history (gcaclower constraint)) (GCAActivatedS history (gcacupper constraint)).
Proof.
  intro activated.
  split.
  + unfold gcaclower.
    induction constraint; simpl in *.
    - destruct (core.(gcclower) constraint) as [ [] | [ node | [ abstract | transitive ] ] ]; simpl.
      * constructor.
      * constructor.
      * constructor.
      * rewrite apply_extend_morphism.
        rewrite apply_extend_morphism.
        rewrite apply_extend_morphism.
        simpl.
        rewrite apply_compose_elimination.
        rewrite apply_eliminate_sum.
        constructor.
    - destruct activated as [ hkeyed activated ].
      merge (history.(gchkeyed) hkeyed) keyed.
      specialize (IHconstraint (history.(gchaction) listener interface hkeyed) activated).
      destruct (gcnclower constraint) as [ [] | [ node | [ transitive | [ parameter | [ abstract | transitive ] ] ] ] ]; simpl.
      * constructor.
      * exists hkeyed.
        assumption.
      * exists hkeyed.
        assumption.
      * assumption.
      * constructor.
      * rewrite apply_extend_morphism.
        rewrite apply_extend_morphism.
        rewrite apply_extend_morphism.
        simpl.
        rewrite apply_compose_elimination.
        rewrite apply_eliminate_sum.
        constructor.
  + unfold gcacupper.
    induction constraint; simpl in *.
    - destruct (core.(gccupper) constraint) as [ listener | [ [] | [ node | [ abstract | transitive ] ] ] ]; simpl.
      * constructor.
      * constructor.
      * constructor.
      * constructor.
      * rewrite apply_extend_morphism.
        rewrite apply_extend_morphism.
        rewrite apply_extend_morphism.
        rewrite apply_extend_morphism.
        simpl.
        rewrite apply_compose_elimination.
        rewrite apply_eliminate_sum.
        constructor.
    - destruct activated as [ hkeyed activated ].
      merge (history.(gchkeyed) hkeyed) keyed.
      specialize (IHconstraint (history.(gchaction) listener interface hkeyed) activated).
      destruct (gcncupper constraint) as [ listener' | [ [] | [ node | [ transitive | [ parameter | [ abstract | transitive ] ] ] ] ] ]; simpl.
      * exists hkeyed.
        assumption.
      * constructor.
      * exists hkeyed.
        assumption.
      * exists hkeyed.
        assumption.
      * assumption.
      * constructor.
      * rewrite apply_extend_morphism.
        rewrite apply_extend_morphism.
        rewrite apply_extend_morphism.
        rewrite apply_extend_morphism.
        simpl.
        rewrite apply_compose_elimination.
        rewrite apply_eliminate_sum.
        constructor.
Qed.



(* Part 5.5: Subhistories
 * One history is a subhistory of another simply if every label-listener resolved by the former is resolved to the same interface by the latter.
 *)

Definition SubHistory {Transitive: Sort} {core: GraphicalCore Transitive} (history history': GCHistory core): SProp
:= forall listener: GCNListener core, forall interface: scheme.(Interface), GCNHKeyedS history listener interface -> GCNHKeyedS history' listener interface.

Lemma shaction {Transitive: Sort} {core: GraphicalCore Transitive} {history history': GCHistory core} (sub: SubHistory history history'): forall listener: core.(GCListener), forall interface: scheme.(Interface), forall hkeyed: history.(GCHKeyedS) listener interface, SubHistory (history.(gchaction) listener interface hkeyed) (history'.(gchaction) listener interface (sub (gcnllistener listener) interface hkeyed)).
Proof.
  intros listener interface hkeyed.
  intros listener' interface' hkeyed'.
  pose proof (sub (gcnlnested listener interface (history.(gchkeyed) hkeyed) listener') interface') as sub'.
  simpl in sub'.
  destruct sub' as [ hkeyed'' hkeyed''' ]; try assumption.
  exists hkeyed.
  assumption.
Qed.

Lemma gcnlactivatedS_subhistory {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history history': GCHistory core}: SubHistory history history' -> forall listener: GCNListener core, GCNLActivatedS history listener -> GCNLActivatedS history' listener.
Proof.
  intros sub listener.
  induction listener as [ Transitive core listener | Transitive core listener interface keyed listener' IHlistener' ]; simpl.
  + trivial.
  + intros [ hkeyed activated ].
    exists (sub (gcnllistener listener) _ hkeyed).
    eapply IHlistener'; try eassumption.
    exact (shaction sub listener interface hkeyed).
Qed.
Lemma gcnnactivatedS_subhistory {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history history': GCHistory core}: SubHistory history history' -> forall node: GCNNode core, GCNNActivatedS history node -> GCNNActivatedS history' node.
Proof.
  intros sub node.
  induction node as [ Transitive core node | Transitive core listener interface keyed node IHnode ]; simpl.
  + trivial.
  + intros [ hkeyed activated ].
    exists (sub (gcnllistener listener) _ hkeyed).
    eapply IHnode; try eassumption.
    exact (shaction sub listener interface hkeyed).
Qed.
Lemma gccactivatedS_subhistory {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history history': GCHistory core}: SubHistory history history' -> forall concrete: GCConcrete core, GCCActivatedS history concrete -> GCCActivatedS history' concrete.
Proof.
  intros sub concrete.
  destruct concrete as [ listener | node | ]; simpl.
  + apply gcnlactivatedS_subhistory.
    assumption.
  + apply gcnnactivatedS_subhistory.
    assumption.
  + trivial.
Qed.
Lemma gcntactivatedS_subhistory {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history history': GCHistory core}: SubHistory history history' -> forall transitive: GCNTransitive core, GCNTActivatedS history transitive -> GCNTActivatedS history' transitive.
Proof.
  intros sub transitive.
  induction transitive as [ Transitive core transitive | Transitive core listener interface keyed parameter | Transitive core listener interface keyed transitive IHtransitive ]; simpl.
  + trivial.
  + apply (sub (gcnllistener listener)).
  + intros [ hkeyed activated ].
    exists (sub (gcnllistener listener) _ hkeyed).
    eapply IHtransitive; try eassumption.
    exact (shaction sub listener interface hkeyed).
Qed.
Lemma gctactivatedS_subhistory {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history history': GCHistory core}: SubHistory history history' -> forall transitive: GCTransitive core, GCTActivatedS history transitive -> GCTActivatedS history' transitive.
Proof.
  intros sub transitive.
  destruct transitive as [ transitive | transitive ]; simpl.
  + apply gcntactivatedS_subhistory.
    assumption.
  + trivial.
Qed.
Lemma gcaactivatedS_subhistory {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history history': GCHistory core}: SubHistory history history' -> forall atom: GCAtom core, GCAActivatedS history atom -> GCAActivatedS history' atom.
Proof.
  intros sub atom.
  destruct atom as [ concrete | transitive ]; simpl.
  + apply gccactivatedS_subhistory.
    assumption.
  + apply gctactivatedS_subhistory.
    assumption.
Qed.
Lemma gcncactivatedS_subhistory {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history history': GCHistory core}: SubHistory history history' -> forall constraint: GCNConstraint core, GCNCActivatedS history constraint -> GCNCActivatedS history' constraint.
Proof.
  intros sub constraint activated.
  induction constraint as [ Transitive core constraint | Transitive core listener interface keyed constraint ]; simpl in *.
  + assumption.
  + destruct activated as [ hkeyed activated ].
    exists (sub (gcnllistener listener) interface hkeyed).
    apply IHconstraint with (history.(gchaction) listener interface hkeyed); try assumption.
    exact (shaction sub listener interface hkeyed).
Qed.



(* Part 5.6: Finality
 * Finality indicates when a history represents a final resolution of label-listeners after an execution of the algorithm.
 * For example, since we do not here support inheritance, every label-listener can be resolved to at most one interface.
 * Similarly, a label-listener cannot be both unresolved and resolved to an interface, but one or the other must hold.
 *)
CoInductive FinalGCHistory {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core}: SProp :=
{ fgchunique [listener: core.(GCListener)] [interface interface': scheme.(Interface)]: history.(GCHKeyedS) listener interface -> history.(GCHKeyedS) listener interface' -> eqS interface interface';
  fgchunresolved (listener: core.(GCListener)) (ur: history.(GCHUnResolvedS) listener): forall interface: scheme.(Interface), history.(GCHKeyedS) listener interface -> FalseS;
  fgchresolved (listener: core.(GCListener)): OrS (history.(GCHUnResolvedS) listener) (existsTS interface: scheme.(Interface), history.(GCHKeyedS) listener interface);
  fgchaction (listener: core.(GCListener)) (interface: scheme.(Interface)) (hkeyed: history.(GCHKeyedS) listener interface): FinalGCHistory (history := history.(gchaction) listener interface hkeyed);
}.
Arguments FinalGCHistory {_ _} _.
Lemma fgcnhunique {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} (final: FinalGCHistory history) [listener: GCNListener core] [interface interface': scheme.(Interface)]: GCNHKeyedS history listener interface -> GCNHKeyedS history listener interface' -> eqS interface interface'.
Proof.
  revert interface interface'.
  induction listener; simpl.
  + apply final.(fgchunique).
  + intros interface' interface'' [ hkeyed nhkeyed' ] [ hkeyed' nhkeyed'' ].
    merge hkeyed hkeyed'.
    eapply IHlistener; try eassumption.
    exact (final.(fgchaction) listener interface hkeyed).
Qed.
Lemma fgcnhunresolved {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} (final: FinalGCHistory history) (listener: GCNListener core) (ur: GCNHUnResolvedS history listener) (interface: scheme.(Interface)) (hkeyed: GCNHKeyedS history listener interface): FalseS.
Proof.
  revert ur interface hkeyed.
  induction listener; simpl in *.
  + apply final.(fgchunresolved).
  + intros [ hkeyed ur ] interface' [ hkeyed' nhkeyed ].
    merge hkeyed hkeyed'.
    revert ur interface' nhkeyed.
    apply IHlistener.
    exact (final.(fgchaction) listener interface hkeyed).
Qed.
Lemma fgcnhresolved {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} (final: FinalGCHistory history) (listener: GCNListener core): GCNLActivatedS history listener -> OrS (GCNHUnResolvedS history listener) (existsTS interface: scheme.(Interface), GCNHKeyedS history listener interface).
Proof.
  intro activated.
  induction listener; simpl in *.
  + apply final.(fgchresolved).
  + destruct activated as [ hkeyed activated ].
    specialize (IHlistener (history.(gchaction) listener interface hkeyed) (final.(fgchaction) listener interface hkeyed) activated).
    destruct IHlistener as [ ur | [ interface' hkeyed' ] ].
    - left.
      exists hkeyed.
      assumption.
    - right.
      exists interface'.
      exists hkeyed.
      assumption.
Qed.

Lemma final_gcmap_history: forall {Transitive Transitive': Sort} (morphism: SortMorphism Transitive Transitive') {core: GraphicalCore Transitive} (history: GCHistory core), FinalGCHistory history -> FinalGCHistory (gcmap_history morphism history).
Proof.
  cofix final_gcmap_history.
  intros Transitive Transitive' morphism core history final.
  constructor; cbn.
  + apply final.(fgchunique).
  + apply final.(fgchunresolved).
  + apply final.(fgchresolved).
  + intros.
    apply final_gcmap_history.
    apply final.(fgchaction).
Qed.



(* Part 5.6: Constraint-Derivation *)

(* Constraint-derivation is defined roughly in line with Figure 14.
 * The treatment of signs is slightly different in order for Rocq to recognize it as strictly positive.
 * Similarly, rather than using a relation on members and components, we found using a binary relation on components along with a lemma ruling out left-hand label-listeners to be more amenable to Rocq.
 *)
Inductive SDerived `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core}: Sign -> GCAtom core -> GCAtom core -> SProp
:= dcontravariant (atom atom': GCAtom core): SDerived negative atom atom' -> SDerived positive atom' atom
 | dconstraint (constraint: GCNConstraint core) (activated: GCNCActivatedS history constraint): SDerived positive (gcaclower constraint) (gcacupper constraint)
 | dtransitive (atom: GCAtom core) (transitive': GCTransitive core) (atom'': GCAtom core): SDerived positive atom (gcatransitive transitive') -> SDerived positive (gcatransitive transitive') atom'' -> SDerived positive atom atom''
 | dnode (node node': GCNNode core) (e: eqS (gcnninterface node) (gcnninterface node')) (parameter: scheme.(IParameter) (gcnninterface node)): SDerived positive (gcaconcrete (gccnode node)) (gcaconcrete (gccnode node')) -> SDerived ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument node parameter)) (apply_elimination (gcatomize core) (gcnnargument node' (convert e scheme.(IParameter) parameter)))
 | dlistener (node: GCNNode core) (listener': GCNListener core) (interface': scheme.(Interface)) (hkeyed': GCNHKeyedS history listener' interface') (e: eqS (gcnninterface node) interface') (parameter: scheme.(IParameter) (gcnninterface node)): SDerived positive (gcaconcrete (gccnode node)) (gcaconcrete (gcclistener listener')) -> SDerived ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument node parameter)) (gcatransitive (gctntransitive (gcntlargument listener' interface' (gcnhkeyed hkeyed') (convert e scheme.(IParameter) parameter)))).
Arguments SDerived {_ _ _} _ _ _ _.
Definition Derived `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core): GCAtom core -> GCAtom core -> SProp
:= SDerived history positive.

Lemma sderived_signed {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (sign: Sign) (atom atom': GCAtom core): SDerived history sign atom atom' -> Signed (Derived history) sign atom atom'.
Proof.
  intro sub.
  destruct sign; simpl; try assumption.
  apply dcontravariant.
  assumption.
Qed.

Lemma gcatomize_not_listener {Transitive: Sort} {core: GraphicalCore Transitive} (listener: GCNListener core) (v: SumSort (cons Unit (cons (GCNNode core) (cons (GCNTransitive core) Transitive)))): gcaconcrete (gcclistener listener) = apply_elimination (gcatomize core) v -> FalseS.
Proof.
  intro e.
  destruct v as [ | [ | [ | v ] ] ]; simpl in e; try discriminate e.
  rewrite apply_compose_elimination in e.
  discriminate e.
Qed.
Lemma gcaclower_not_listener {Transitive: Sort} {core: GraphicalCore Transitive} (constraint: GCNConstraint core) (listener: GCNListener core): gcaconcrete (gcclistener listener) = gcaclower constraint -> FalseS.
Proof.
  apply gcatomize_not_listener.
Qed.
Lemma derived_listener_false {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} (listener: GCNListener core) (atom': GCAtom core): Derived history (gcaconcrete (gcclistener listener)) atom' -> FalseS.
Proof.
  remember (gcaconcrete (gcclistener listener)) as atom.
  symmetry in Heqatom.
  unfold Derived.
  change (match positive with negative => gcaconcrete (gcclistener listener) = atom' | positive => gcaconcrete (gcclistener listener) = atom end) in Heqatom.
  revert Heqatom.
  generalize positive.
  intros sign e derived.
  induction derived.
  + auto.
  + apply gcaclower_not_listener in e.
    assumption.
  + auto.
  + clear derived IHderived.
    destruct ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter).
    - apply gcatomize_not_listener in e.
      assumption.
    - apply gcatomize_not_listener in e.
      assumption.
  + clear derived IHderived.
    destruct ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter).
    - inversion e.
    - apply gcatomize_not_listener in e.
      assumption.
Qed.

Lemma sderived_activated {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {sign: Sign} {atom atom': GCAtom core}: SDerived history sign atom atom' -> AndS (GCAActivatedS history atom) (GCAActivatedS history atom').
Proof.
  intro derived.
  induction derived.
  + split; apply IHderived.
  + apply constraint_activated.
    assumption.
  + split.
    - apply IHderived1.
    - apply IHderived2.
  + simpl in IHderived.
    destruct IHderived as [ IHderived IHderived' ].
    split.
    - apply gcnnargument_activated.
      assumption.
    - apply gcnnargument_activated.
      assumption.
  + simpl in IHderived.
    destruct IHderived as [ IHderived IHderived' ].
    split.
    - apply gcnnargument_activated.
      assumption.
    - simpl.
      apply gcntlargument_activated.
      assumption.
Qed.

Lemma derived_subhistory {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history history': GCHistory core}: SubHistory history history' -> forall sign: Sign, forall atom atom': GCAtom core, SDerived history sign atom atom' -> SDerived history' sign atom atom'.
Proof.
  intros sub sign atom atom' derived.
  induction derived.
  + apply dcontravariant.
    assumption.
  + apply dconstraint.
    apply (gcncactivatedS_subhistory sub).
    assumption.
  + apply dtransitive with transitive'; assumption.
  + apply dnode.
    assumption.
  + merge (gcnhkeyed (sub listener' interface' hkeyed')) (gcnhkeyed hkeyed').
    apply dlistener.
    assumption.
Qed.



(* Part 6: Models
 * Here we define modeling and a graphical core's type space.
 *)

(* Part 6.1: Models *)

(* Model and ModelV, combined, correspond to the definition of models in Figure 16 of the paper.
 * We only define models with respect to a specific history; uses of modeling directly with respect to a graphical core in the paper are always inlined in our mechanization.
 *)
CoInductive Model {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace}: Type :=
{ mabstract (abstract: core.(GCAbstract)): space.(SpaceType);
  mlistener (listener: core.(GCListener)): space.(SpaceType);
  mnode (node: core.(GCNode)): space.(SpaceType);
  mlargument (listener: core.(GCListener)) (interface: scheme.(Interface)) (hkeyed: history.(GCHKeyedS) listener interface) (parameter: scheme.(IParameter) interface): space.(SpaceType);
  mlaction (listener: core.(GCListener)) (interface: scheme.(Interface)) (hkeyed: history.(GCHKeyedS) listener interface): Model (history := history.(gchaction) listener interface hkeyed);
}.
Arguments Model {_ _} _ _.
Definition melimination {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (elimination: SortElimination space.(SpaceType) Transitive) (model: Model history space): SortElimination space.(SpaceType) (cons Unit (cons core.(GCNode) (cons core.(GCAbstract) Transitive)))
:= pair_elimination (fun _ => space.(stany)) (pair_elimination model.(mnode) (pair_elimination model.(mabstract) elimination)).
Definition meliminate {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (elimination: SortElimination space.(SpaceType) Transitive) (model: Model history space): SumSort (cons Unit (cons core.(GCNode) (cons core.(GCAbstract) Transitive))) -> space.(SpaceType)
:= apply_elimination (melimination elimination model).
Definition meliminationl {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (elimination: SortElimination space.(SpaceType) Transitive) (model: Model history space): SortElimination space.(SpaceType) (cons core.(GCListener) (cons Unit (cons core.(GCNode) (cons core.(GCAbstract) Transitive))))
:= pair_elimination model.(mlistener) (melimination elimination model).
Definition meliminatel {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (elimination: SortElimination space.(SpaceType) Transitive) (model: Model history space): SumSort (cons core.(GCListener) (cons Unit (cons core.(GCNode) (cons core.(GCAbstract) Transitive)))) -> space.(SpaceType)
:= apply_elimination (meliminationl elimination model).

CoInductive ModelV {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} {model: Model history space} {elimination: SortElimination space.(SpaceType) Transitive}: SProp :=
{ mconstraintv (constraint: core.(GCConstraint)): space.(SubSpaceType) (meliminate elimination model (core.(gcclower) constraint)) (meliminatel elimination model (core.(gccupper) constraint));
  mlowerv (node: core.(GCNode)): space.(SubSpaceType) (space.(stinterface) (core.(gcninterface) node) (fun parameter => meliminate elimination model (core.(gcnargument) node parameter))) (model.(mnode) node);
  mupperv (node: core.(GCNode)): space.(SubSpaceType) (model.(mnode) node) (space.(stinterface) (core.(gcninterface) node) (fun parameter => meliminate elimination model (core.(gcnargument) node parameter)));
  mlargumentv (listener: core.(GCListener)) (interface: scheme.(Interface)) (hkeyed: history.(GCHKeyedS) listener interface): space.(SubSpaceType) (model.(mlistener) listener) (space.(stinterface) interface (model.(mlargument) listener interface hkeyed));
  mlactionv (listener: core.(GCListener)) (interface: scheme.(Interface)) (hkeyed: history.(GCHKeyedS) listener interface): ModelV (model := model.(mlaction) listener interface hkeyed) (elimination := pair_elimination (model.(mlargument) listener interface hkeyed) (pair_elimination model.(mabstract) elimination)) (history := history.(gchaction) listener interface hkeyed);
  munresolvedv (listener: core.(GCListener)) (ur: history.(GCHUnResolvedS) listener): space.(UnReachable) (model.(mlistener) listener);
}.
Arguments ModelV {_ _ _ _} _.

Definition gcmap_model: forall {Transitive Transitive': Sort} (morphism: SortMorphism Transitive Transitive') {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space), Model (gcmap_history morphism history) space
:= cofix gcmap_model {Transitive Transitive': Sort} (morphism: SortMorphism Transitive Transitive') {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space): Model (gcmap_history morphism history) space
:= Build_Model Transitive' (gcmap morphism core) (gcmap_history morphism history) space
               model.(mabstract)
               model.(mlistener)
               model.(mnode)
               model.(mlargument)
               (fun listener interface keyed => gcmap_model _ (model.(mlaction) listener interface keyed)).
Lemma gcmap_modelv: forall {Transitive Transitive': Sort} (morphism: SortMorphism Transitive Transitive') {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (elimination: SortElimination space.(SpaceType) Transitive'), ModelV model (eliminate_morphism morphism elimination) -> ModelV (gcmap_model morphism model) elimination.
Proof.
  cofix gcmap_modelv.
  intros Transitive Transitive' morphism core history space model elimination vmodel.
  constructor.
  + intro constraint.
    cbn.
    unfold meliminatel.
    unfold meliminationl.
    rewrite <- apply_eliminate_morphism.
    rewrite eliminate_consid_pair_elimination.
    unfold meliminate.
    unfold melimination.
    rewrite <- apply_eliminate_morphism.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_consid_pair_elimination.
    apply vmodel.(mconstraintv).
  + intro node.
    eapply space.(ssttrans); try apply vmodel.(mlowerv).
    apply space.(sstvariance).
    intro parameter.
    cbn.
    unfold meliminate.
    unfold melimination.
    rewrite <- apply_eliminate_morphism.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_consid_pair_elimination.
    apply signed_refl.
    apply space.(sstrefl).
  + intro node.
    eapply space.(ssttrans); try apply vmodel.(mupperv).
    apply space.(sstvariance).
    intro parameter.
    cbn.
    unfold meliminate.
    unfold melimination.
    rewrite <- apply_eliminate_morphism.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_consid_pair_elimination.
    apply signed_refl.
    apply space.(sstrefl).
  + apply vmodel.(mlargumentv).
  + cbn.
    intros listener interface hkeyed.
    apply gcmap_modelv.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_consid_pair_elimination.
    apply vmodel.(mlactionv).
  + apply vmodel.(munresolvedv).
Qed.



(* Part 6.2: The Type Space of a Graphical Core
 * This definition is in line with Figure 18 of the paper.
 *)

Inductive GCType {Transitive: Sort} {core: GraphicalCore Transitive}: Type
:= gctatom (atom: GCAtom core)
 | gctinterface (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> GCType).
Arguments GCType {_} _.
Inductive SubGCType `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core}: GCType core -> GCType core -> SProp
:= sgctrefl (type: GCType core): SubGCType type type
 | sgcttrans (type type' type'': GCType core): SubGCType type type' -> SubGCType type' type'' -> SubGCType type type''
 | sgctvariance (interface: scheme.(Interface)) (arguments arguments': scheme.(IParameter) interface -> GCType core): (forall parameter: scheme.(IParameter) interface, ISigned SubGCType ((hierarchy.(hinterface) interface).(uisvariance) parameter) (arguments parameter) (arguments' parameter)) -> SubGCType (gctinterface interface arguments) (gctinterface interface arguments')
 | sgctinheritance (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> GCType core): SubGCType (gctinterface interface arguments) (gctatom (gcaconcrete gccany))
 | sgctderived (atom: GCAtom core) (atom': GCAtom core): Derived history atom atom' -> SubGCType (gctatom atom) (gctatom atom')
 | sgctlower (node: GCNNode core): SubGCType (gctinterface (gcnninterface node) (fun parameter => gctatom (apply_elimination (gcatomize core) (gcnnargument node parameter)))) (gctatom (gcaconcrete (gccnode node)))
 | sgctupper (node: GCNNode core): SubGCType (gctatom (gcaconcrete (gccnode node))) (gctinterface (gcnninterface node) (fun parameter => gctatom (apply_elimination (gcatomize core) (gcnnargument node parameter))))
 | sgctlistener (listener: GCNListener core) (interface: scheme.(Interface)) (hkeyed: GCNHKeyedS history listener interface): SubGCType (gctatom (gcaconcrete (gcclistener listener))) (gctinterface interface (fun parameter => gctatom (gcatransitive (gctntransitive (gcntlargument listener interface (gcnhkeyed hkeyed) parameter))))).
Arguments SubGCType {_ _ _} _ _ _.
Inductive UnReachableGC `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core}: GCType core -> SProp
:= urgctrans (type type': GCType core): SubGCType history type type' -> UnReachableGC type' -> UnReachableGC type
 | urgcunreachable (listener: GCNListener core): GCNHUnResolvedS history listener -> UnReachableGC (gctatom (gcaconcrete (gcclistener listener))).
Arguments UnReachableGC {_ _ _} _ _.
Definition GCTypeSpace `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core): TypeSpace :=
{| SpaceType := GCType core;
   stany := gctatom (gcaconcrete gccany);
   stinterface := gctinterface;
   SubSpaceType := SubGCType history;
   sstrefl := sgctrefl;
   ssttrans := sgcttrans;
   sstvariance interface arguments arguments' sub := sgctvariance interface arguments arguments' (fun parameter => signed_isigned (sub parameter));
   sstinheritance := sgctinheritance;
   UnReachable := UnReachableGC history;
   sstur := urgctrans;
|}.

Lemma sderived_sgct `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (sign: Sign) (atom atom': GCAtom core): SDerived history sign atom atom' -> Signed (SubGCType history) sign (gctatom atom) (gctatom atom').
Proof.
  intro sub.
  apply sderived_signed in sub.
  destruct sign; apply sgctderived; assumption.
Qed.



(* Part 6.3: Modeling with a graphical core's type space
 * Here we prove Lemma 9.4 of the paper.
 *)

Definition gctsnmodel (space: TypeSpace): forall {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core), (GCNTransitive core -> space.(SpaceType)) -> (GCNListener core -> space.(SpaceType)) -> (GCNNode core -> space.(SpaceType)) -> Model history space
:= cofix gctsnmodel {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (transitives: GCNTransitive core -> space.(SpaceType)) (listeners: GCNListener core -> space.(SpaceType)) (nodes: GCNNode core -> space.(SpaceType)): Model history space :=
{| mabstract := compose gcntabstract transitives;
   mlistener := compose gcnllistener listeners;
   mnode := compose gcnnnode nodes;
   mlargument listener interface hkeyed := compose (gcntargument listener interface (history.(gchkeyed) hkeyed)) transitives;
   mlaction listener interface hkeyed := gctsnmodel (history.(gchaction) listener interface hkeyed) (compose (gcntnested listener interface (history.(gchkeyed) hkeyed)) transitives) (compose (gcnlnested listener interface (history.(gchkeyed) hkeyed)) listeners) (compose (gcnnnested listener interface (history.(gchkeyed) hkeyed)) nodes);
|}.
Definition gctsmodel `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core): Model history (GCTypeSpace history)
:= gctsnmodel (GCTypeSpace history) history (compose (compose gctntransitive gcatransitive) gctatom) (compose (compose gcclistener gcaconcrete) gctatom) (compose (compose gccnode gcaconcrete) gctatom).

Lemma gctsnmodelv (space: TypeSpace)
        : forall {Transitive: Sort}
                 {core: GraphicalCore Transitive}
                 (history: GCHistory core)
                 (transitives: GCNTransitive core -> space.(SpaceType))
                 (listeners: GCNListener core -> space.(SpaceType))
                 (nodes: GCNNode core -> space.(SpaceType))
                 (elimination: SortElimination space.(SpaceType) Transitive),
          (forall constraint: GCNConstraint core, GCNCActivatedS history constraint -> space.(SubSpaceType) (apply_elimination (pair_elimination (fun _ => space.(stany)) (pair_elimination nodes (pair_elimination transitives elimination))) (gcnclower constraint)) (apply_elimination (pair_elimination listeners (pair_elimination (fun _ => space.(stany)) (pair_elimination nodes (pair_elimination transitives elimination)))) (gcncupper constraint)))
       -> (forall node: GCNNode core, space.(SubSpaceType) (space.(stinterface) (gcnninterface node) (fun parameter => apply_elimination (pair_elimination (fun _ => space.(stany)) (pair_elimination nodes (pair_elimination transitives elimination))) (gcnnargument node parameter))) (nodes node))
       -> (forall node: GCNNode core, space.(SubSpaceType) (nodes node) (space.(stinterface) (gcnninterface node) (fun parameter => apply_elimination (pair_elimination (fun _ => space.(stany)) (pair_elimination nodes (pair_elimination transitives elimination))) (gcnnargument node parameter))))
       -> (forall listener: GCNListener core, forall interface: scheme.(Interface), forall hkeyed: GCNHKeyedS history listener interface, space.(SubSpaceType) (listeners listener) (space.(stinterface) interface (compose (gcntlargument listener interface (gcnhkeyed hkeyed)) transitives)))
       -> (forall listener: GCNListener core, GCNHUnResolvedS history listener -> space.(UnReachable) (listeners listener))
       -> ModelV (gctsnmodel space history transitives listeners nodes) elimination.
Proof.
  cofix gctsnmodelv.
  intros Transitive core history transitives listeners nodes elimination constraints interfaces interfaces' arguments unreachables.
  constructor.
  + intro constraint.
    specialize (constraints (gcncconstraint constraint) trueS).
    cbn in constraints.
    rewrite <- apply_eliminate_morphism in constraints.
    rewrite <- apply_eliminate_morphism in constraints.
    rewrite eliminate_cons_pair_elimination in constraints.
    rewrite eliminate_consid_pair_elimination in constraints.
    rewrite eliminate_cons_pair_elimination in constraints.
    rewrite eliminate_cons_pair_elimination in constraints.
    rewrite eliminate_id_morphism in constraints.
    assumption.
  + intro node.
    specialize (interfaces (gcnnnode node)).
    eapply ssttrans; try apply interfaces; clear interfaces.
    apply sstvariance.
    intro parameter.
    cbn.
    rewrite <- apply_eliminate_morphism.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_id_morphism.
    apply signed_refl.
    apply sstrefl.
  + intro node.
    specialize (interfaces' (gcnnnode node)).
    eapply ssttrans; try apply interfaces'; clear interfaces'.
    apply sstvariance.
    intro parameter.
    cbn.
    rewrite <- apply_eliminate_morphism.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_id_morphism.
    apply signed_refl.
    apply sstrefl.
  + intros listener interface hkeyed.
    apply (arguments (gcnllistener listener) interface hkeyed).
  + intros listener interface hkeyed.
    cbn.
    apply gctsnmodelv.
    - clear interfaces interfaces' arguments unreachables.
      intros constraint activated.
      specialize (constraints (gcncnested listener interface (history.(gchkeyed) hkeyed) constraint) (ex_introSS _ _ hkeyed activated)).
      cbn in constraints.
      rewrite <- apply_eliminate_morphism in constraints.
      rewrite <- apply_eliminate_morphism in constraints.
      rewrite eliminate_cons_pair_elimination in constraints.
      rewrite eliminate_consid_pair_elimination in constraints.
      rewrite eliminate_cons_pair_elimination in constraints.
      rewrite eliminate_pair_morphism in constraints.
      rewrite eliminate_pair_morphism in constraints.
      rewrite eliminate_select_head_pair_elimination in constraints.
      rewrite eliminate_select_head_pair_elimination in constraints.
      rewrite eliminate_cons_pair_elimination in constraints.
      rewrite eliminate_id_morphism in constraints.
      assumption.
    - clear constraints interfaces' arguments unreachables.
      intro node.
      specialize (interfaces (gcnnnested listener interface (history.(gchkeyed) hkeyed) node)).
      cbn in interfaces.
      eapply ssttrans; try apply interfaces; clear interfaces.
      apply sstvariance.
      intro parameter.
      rewrite <- apply_eliminate_morphism.
      rewrite eliminate_consid_pair_elimination.
      rewrite eliminate_cons_pair_elimination.
      rewrite eliminate_pair_morphism.
      rewrite eliminate_pair_morphism.
      rewrite eliminate_select_head_pair_elimination.
      rewrite eliminate_select_head_pair_elimination.
      rewrite eliminate_cons_pair_elimination.
      rewrite eliminate_id_morphism.
      apply signed_refl.
      apply sstrefl.
    - clear constraints interfaces arguments unreachables.
      intro node.
      specialize (interfaces' (gcnnnested listener interface (history.(gchkeyed) hkeyed) node)).
      cbn in interfaces'.
      eapply ssttrans; try apply interfaces'; clear interfaces'.
      apply sstvariance.
      intro parameter.
      rewrite <- apply_eliminate_morphism.
      rewrite eliminate_consid_pair_elimination.
      rewrite eliminate_cons_pair_elimination.
      rewrite eliminate_pair_morphism.
      rewrite eliminate_pair_morphism.
      rewrite eliminate_select_head_pair_elimination.
      rewrite eliminate_select_head_pair_elimination.
      rewrite eliminate_cons_pair_elimination.
      rewrite eliminate_id_morphism.
      apply signed_refl.
      apply sstrefl.
    - clear constraints interfaces interfaces' unreachables.
      intros listener' interface' hkeyed'.
      exact (arguments (gcnlnested listener interface (history.(gchkeyed) hkeyed) listener') interface' (ex_introSS _ _ hkeyed hkeyed')).
    - intros listener' unresolved'.
      exact (unreachables (gcnlnested listener interface (history.(gchkeyed) hkeyed) listener') (ex_introSS _ _ hkeyed unresolved')).
  + intros listener unresolved.
    exact (unreachables (gcnllistener listener) unresolved).
Qed.
Lemma gctsmodelv {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core): ModelV (gctsmodel history) (compose_elimination (eliminate_sum gcttransitive) (compose gcatransitive gctatom)).
Proof.
  apply gctsnmodelv; cbn.
  + intros constraint activated.
    pose proof (dconstraint (history := history) constraint activated) as sub.
    apply sgctderived in sub.
    unfold gcaclower in sub.
    unfold gcacupper in sub.
    rewrite <- (apply_compose_elimination _ gctatom) in sub.
    rewrite <- (apply_compose_elimination _ gctatom) in sub.
    unfold gcatomizel in sub.
    rewrite compose_pair_elimination in sub.
    unfold gcatomize in sub.
    rewrite compose_pair_elimination in sub.
    rewrite compose_pair_elimination in sub.
    rewrite compose_pair_elimination in sub.
    rewrite compose_compose_elimination in sub.
    assumption.
  + intro node.
    pose proof (sgctlower (history := history) node) as sub.
    eapply sgcttrans; try apply sub; clear sub.
    apply sgctvariance.
    intro parameter.
    unfold gcatomize.
    rewrite <- (apply_compose_elimination _ gctatom).
    rewrite compose_pair_elimination.
    rewrite compose_pair_elimination.
    rewrite compose_pair_elimination.
    rewrite compose_compose_elimination.
    apply signed_isigned.
    apply signed_refl.
    apply sgctrefl.
  + intro node.
    pose proof (sgctupper (history := history) node) as sub.
    eapply sgcttrans; try apply sub; clear sub.
    apply sgctvariance.
    intro parameter.
    unfold gcatomize.
    rewrite <- (apply_compose_elimination _ gctatom).
    rewrite compose_pair_elimination.
    rewrite compose_pair_elimination.
    rewrite compose_pair_elimination.
    rewrite compose_compose_elimination.
    apply signed_isigned.
    apply signed_refl.
    apply sgctrefl.
  + intros listener interface hkeyed.
    exact (sgctlistener (history := history) listener interface hkeyed).
  + intros listener unresolved.
    exact (urgcunreachable (history := history) listener unresolved).
Qed.



(* Part 7: Graphical-Core Consistency
 * Here we define consistency of a graphical core using a given history, in line with Figure 15 of the paper.
 *)

(* ConsistentGCC indicates when two concrete types are shallowly consistent.
 * That is, just looking at their labels (and ignoring any nested components), it indicates whether those labels are consistent.
 *)
Definition ConsistentGCC `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (concrete concrete': GCConcrete core): SProp
:= match concrete, concrete' with
   | gcclistener _, gcclistener _ => TrueS
   | gcclistener _, gccnode _ => TrueS
   | gcclistener listener, gccany => TrueS
   | gccnode node, gcclistener listener' => GCNHKeyedS history listener' (gcnninterface node)
   | gccnode node, gccnode node' => eqS (gcnninterface node) (gcnninterface node')
   | gccnode node, gccany => TrueS
   | gccany, gcclistener _ => FalseS
   | gccany, gccnode _ => FalseS
   | gccany, gccany => TrueS
   end.
(* ConsistentGCA extends ConsistentGCC to indicate when two arbitrary types are shallowly consistent.
 * This is trivially true if either type is non-concrete, since shallowness ignores things like upper and lower bounds (just as it ignores things like nested components).
 *)
Definition ConsistentGCA `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (atom atom': GCAtom core): SProp
:= match atom, atom' with
   | gcaconcrete concrete, gcaconcrete concrete' => ConsistentGCC history concrete concrete'
   | gcaconcrete _, gcatransitive _ => TrueS
   | gcatransitive _, gcaconcrete _ => TrueS
   | gcatransitive _, gcatransitive _ => TrueS
   end.
(* ConsistentGC uses ConsistentGCA to indicate when a graphical core is consistent using a given history.
 * In particular, it addresses the shallowness of ConsistentGCA by considering consistency of all derived constraints (which incorporate considerations like bounds and nested components), not just of activated constraints.
 *)
Definition ConsistentGC `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core): SProp
:= forall atom atom': GCAtom core, Derived history atom atom' -> ConsistentGCA history atom atom'.



(* Part 8: Correspondence
 * Here we prove the correspondence between our notions of consistency for type spaces and for graphical cores.
 *)

(* Part 8.1: Coalgebraic Subtyping
 * We defined subtyping for a graphical core's type space inductively so that it trivially has the required algebraic structure.
 * Here we define a coalgebraic notion of subtyping on the same set of types, and we prove that consistency of the graphical core ensures this has the required algebraic structure.
 *)

(* Two interface types are coalgebraic subtypes only if they are equal and there arguments are (inductive) subtypes (modulo variance). *)
Inductive SubInterface `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {interface: scheme.(Interface)} {arguments: scheme.(IParameter) interface -> GCType core}: forall (interface': scheme.(Interface)) (arguments': scheme.(IParameter) interface' -> GCType core), SProp
:= sivariance (arguments': scheme.(IParameter) interface -> GCType core): (forall parameter: scheme.(IParameter) interface, Signed (SubGCType history) ((hierarchy.(hinterface) interface).(uisvariance) parameter) (arguments parameter) (arguments' parameter)) -> SubInterface interface arguments'.
Arguments SubInterface {_ _ _} _ _ _ _ _.
Lemma sivariance_eqS {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> GCType core) (interface': scheme.(Interface)) (arguments': scheme.(IParameter) interface' -> GCType core): forall e: eqS interface interface', (forall parameter: scheme.(IParameter) interface, Signed (SubGCType history) ((hierarchy.(hinterface) interface).(uisvariance) parameter) (arguments parameter) (arguments' (convert e scheme.(IParameter) parameter))) -> SubInterface history interface arguments interface' arguments'.
Proof.
  intro e.
  destruct (eqS_eq e); rewrite convert_id; clear e.
  apply sivariance.
Qed.
Lemma si_refl {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> GCType core): SubInterface history interface arguments interface arguments.
Proof.
  apply sivariance.
  intro parameter.
  apply signed_refl.
  apply sgctrefl.
Qed.
Lemma si_trans {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> GCType core) (interface': scheme.(Interface)) (arguments': scheme.(IParameter) interface' -> GCType core) (interface'': scheme.(Interface)) (arguments'': scheme.(IParameter) interface'' -> GCType core): SubInterface history interface arguments interface' arguments' -> SubInterface history interface' arguments' interface'' arguments'' -> SubInterface history interface arguments interface'' arguments''.
Proof.
  intros sub sub'.
  destruct sub as [ arguments' sub ].
  destruct sub' as [ arguments'' sub' ].
  apply sivariance.
  intro parameter.
  eapply signed_trans; try apply sgcttrans; eauto.
Qed.

(* The following effectively break down a large binary pattern-match on concrete types into smaller parts that are shared across many cases. *)
Definition SubAnyConcrete `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (concrete': GCConcrete core): SProp
:= match concrete' with
   | gcclistener _ => FalseS
   | gccnode _ => FalseS
   | gccany => TrueS
   end.
Definition SubConcreteAny `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (concrete: GCConcrete core): SProp
:= match concrete with
   | gcclistener listener => existsTS interface: scheme.(Interface), GCNHKeyedS history listener interface
   | gccnode _ => TrueS
   | gccany => TrueS
   end.
Definition SubInterfaceConcrete `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> GCType core) (concrete': GCConcrete core): SProp
:= match concrete' with
   | gcclistener listener' => existsTSS node': GCNNode core, SubInterface history interface arguments (gcnninterface node') (fun parameter' => gctatom (apply_elimination (gcatomize core) (gcnnargument node' parameter'))) & Derived history (gcaconcrete (gccnode node')) (gcaconcrete (gcclistener listener'))
   | gccnode node' => SubInterface history interface arguments (gcnninterface node') (fun parameter' => gctatom (apply_elimination (gcatomize core) (gcnnargument node' parameter')))
   | gccany => TrueS
   end.
Definition SubConcreteInterface `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (concrete: GCConcrete core) (interface': scheme.(Interface)) (arguments': scheme.(IParameter) interface' -> GCType core): SProp
:= match concrete with
   | gcclistener listener => existsTS interface: scheme.(Interface), existsSS hkeyed: GCNHKeyedS history listener interface, SubInterface history interface (fun parameter => gctatom (gcatransitive (gctntransitive (gcntlargument listener interface (gcnhkeyed hkeyed) parameter)))) interface' arguments'
   | gccnode node => SubInterface history (gcnninterface node) (fun parameter => gctatom (apply_elimination (gcatomize core) (gcnnargument node parameter))) interface' arguments'
   | gccany => FalseS
   end.
Definition SubConcrete `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (concrete concrete': GCConcrete core): SProp
:= match concrete with
   | gcclistener listener => OrS (eqS (gcclistener listener) concrete')
                                 (existsTS interface: scheme.(Interface), existsSS hkeyed: GCNHKeyedS history listener interface, SubInterfaceConcrete history interface (fun parameter => gctatom (gcatransitive (gctntransitive (gcntlargument listener interface (gcnhkeyed hkeyed) parameter)))) concrete')
   | gccnode node => SubInterfaceConcrete history (gcnninterface node) (fun parameter => gctatom (apply_elimination (gcatomize core) (gcnnargument node parameter))) concrete'
   | gccany => eqS gccany concrete'
   end.

Lemma sc_refl {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (concrete: GCConcrete core): SubConcrete history concrete concrete.
Proof.
  destruct concrete as [ listener | node | ]; simpl.
  + left.
    reflexivity.
  + apply si_refl.
  + reflexivity.
Qed.

(* Here we extend that pattern-match on concrete types to all types. *)
Definition SubGCType' `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (type type': GCType core): SProp
:= match type, type' with
   | gctatom (gcaconcrete concrete), gctatom (gcaconcrete concrete') => SubConcrete history concrete concrete'
   | gctatom (gcaconcrete concrete), gctatom (gcatransitive transitive') => existsTSS concrete': GCConcrete core, SubConcrete history concrete concrete' & Derived history (gcaconcrete concrete') (gcatransitive transitive')
   | gctatom (gcatransitive transitive), gctatom (gcaconcrete concrete') => existsTSS concrete: GCConcrete core, Derived history (gcatransitive transitive) (gcaconcrete concrete) & SubConcrete history concrete concrete'
   | gctatom (gcatransitive transitive), gctatom (gcatransitive transitive') => OrS (eqS transitive transitive')
                                                                               (OrS (Derived history (gcatransitive transitive) (gcatransitive transitive'))
                                                                                    (existsTSS concrete: GCConcrete core, Derived history (gcatransitive transitive) (gcaconcrete concrete) & existsTSS concrete': GCConcrete core, SubConcrete history concrete concrete' & Derived history (gcaconcrete concrete') (gcatransitive transitive')))
   | gctinterface interface arguments, gctatom (gcaconcrete concrete') => SubInterfaceConcrete history interface arguments concrete'
   | gctinterface interface arguments, gctatom (gcatransitive transitive') => existsTSS concrete': GCConcrete core, SubInterfaceConcrete history interface arguments concrete' & Derived history (gcaconcrete concrete') (gcatransitive transitive')
   | gctinterface interface arguments, gctinterface interface' arguments' => SubInterface history interface arguments interface' arguments'
   | gctatom (gcaconcrete concrete), gctinterface interface' arguments' => SubConcreteInterface history concrete interface' arguments'
   | gctatom (gcatransitive transitive), gctinterface interface' arguments' => existsTSS concrete: GCConcrete core, Derived history (gcatransitive transitive) (gcaconcrete concrete) & SubConcreteInterface history concrete interface' arguments'
   end.

(* Coalgebraic subtyping is reflexive. *)
Lemma sgct_refl' {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (type: GCType core): SubGCType' history type type.
Proof.
  destruct type as [ [ concrete | transitive ] | interface arguments ]; simpl.
  + apply sc_refl.
  + left.
    reflexivity.
  + apply si_refl.
Qed.

(* Assuming consistency, derived constraints between concrete types imply they are coalgebraic subtypes.
 * For example, if we have two interface types, then consistency implies the two interfaces are equal, in which case constraint-derivation ensures derived constraints between their arguments.
 *)
Lemma derived_sc {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (concrete concrete': GCConcrete core): ConsistentGC history -> Derived history (gcaconcrete concrete) (gcaconcrete concrete') -> SubConcrete history concrete concrete'.
Proof.
  intros consistent derived.
  destruct concrete as [ listener | node | ]; simpl.
  + right.
    apply derived_listener_false in derived.
    destruct derived.
  + destruct concrete' as [ listener' | node' | ]; simpl.
    - exists node; try assumption.
      apply si_refl.
    - pose proof derived as e.
      apply consistent in e.
      apply sivariance_eqS with e.
      intro parameter.
      apply sderived_sgct.
      apply dnode.
      assumption.
    - constructor.
  + pose proof derived as e.
    apply consistent in e.
    destruct concrete' as [ listener' | node' | ].
    - destruct e.
    - destruct e.
    - reflexivity.
Qed.

(* The following prove transitivity for various specific cases of types. *)
Lemma si_sic {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> GCType core) (interface': scheme.(Interface)) (arguments': scheme.(IParameter) interface' -> GCType core) (concrete'': GCConcrete core): SubInterface history interface arguments interface' arguments' -> SubInterfaceConcrete history interface' arguments' concrete'' -> SubInterfaceConcrete history interface arguments concrete''.
Proof.
  intros sub sub'.
  destruct concrete'' as [ listener'' | node'' | ]; simpl in *.
  + destruct sub' as [ node' sub' derived' ].
    exists node'; try assumption.
    apply si_trans with interface' arguments'; assumption.
  + apply si_trans with interface' arguments'; assumption.
  + constructor.
Qed.
Lemma sic_sc {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> GCType core) (concrete' concrete'': GCConcrete core): ConsistentGC history -> FinalGCHistory history -> SubInterfaceConcrete history interface arguments concrete' -> SubConcrete history concrete' concrete'' -> SubInterfaceConcrete history interface arguments concrete''.
Proof.
  intros consistent final sub sub'.
  destruct concrete' as [ listener' | node' | ]; simpl in *.
  + destruct sub as [ node sub derived ].
    destruct sub' as [ e' | [ interface' [ hkeyed' sub' ] ] ].
    - destruct e'.
      eapply si_sic; try eassumption.
      simpl.
      exists node; try assumption.
      apply si_refl.
    - eapply si_sic; try apply sub'; clear sub'.
      eapply si_trans; try apply sub; clear sub.
      pose proof derived as hkeyed.
      apply consistent in hkeyed.
      pose proof hkeyed' as e.
      apply (fgcnhunique final hkeyed) in e.
      destruct e.
      apply sivariance.
      intro parameter.
      apply sderived_sgct.
      apply dlistener with (hkeyed' := hkeyed') (e := eqS_refl _) (parameter := parameter) in derived.
      rewrite convert_id in derived.
      eassumption.
  + eapply si_sic; eassumption.
  + destruct sub'.
    simpl.
    constructor.
Qed.
Lemma sc_trans {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (concrete concrete' concrete'': GCConcrete core): ConsistentGC history -> FinalGCHistory history -> SubConcrete history concrete concrete' -> SubConcrete history concrete' concrete'' -> SubConcrete history concrete concrete''.
Proof.
  intros consistent final sub sub'.
  destruct concrete as [ listener | node | ]; simpl in *.
  + destruct sub as [ e | [ interface [ hkeyed sub ] ] ].
    - destruct e; simpl in *.
      assumption.
    - right.
      exists interface.
      exists hkeyed.
      eapply sic_sc; eassumption.
  + eapply sic_sc; eassumption.
  + destruct sub.
    simpl in sub'.
    assumption.
Qed.
Lemma sic_sci {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (interface: scheme.(Interface)) (arguments: scheme.(IParameter) interface -> GCType core) (concrete': GCConcrete core) (interface'': scheme.(Interface)) (arguments'': scheme.(IParameter) interface'' -> GCType core): ConsistentGC history -> FinalGCHistory history -> SubInterfaceConcrete history interface arguments concrete' -> SubConcreteInterface history concrete' interface'' arguments'' -> SubInterface history interface arguments interface'' arguments''.
Proof.
  intros consistent final sub sub'.
  destruct concrete' as [ listener' | node' | ]; simpl in *.
  + destruct sub as [ node sub derived ].
    destruct sub' as [ interface' [ hkeyed' sub' ] ].
    eapply si_trans; try eassumption; clear sub.
    eapply si_trans; try eassumption; clear sub'.
    pose proof derived as hkeyed.
    apply consistent in hkeyed.
    pose proof hkeyed' as e.
    apply (fgcnhunique final hkeyed) in e.
    destruct e.
    constructor.
    intro parameter.
    apply sderived_sgct.
    apply dlistener with (hkeyed' := hkeyed') (e := eqS_refl _) (parameter := parameter) in derived.
    rewrite convert_id in derived.
    assumption.
  + eapply si_trans; eassumption.
  + destruct sub'.
Qed.
Lemma sc_sci {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (concrete concrete': GCConcrete core) (interface'': scheme.(Interface)) (arguments'': scheme.(IParameter) interface'' -> GCType core): ConsistentGC history -> FinalGCHistory history -> SubConcrete history concrete concrete' -> SubConcreteInterface history concrete' interface'' arguments'' -> SubConcreteInterface history concrete interface'' arguments''.
Proof.
  intros consistent final sub sub'.
  destruct concrete as [ listener | node | ]; simpl in *.
  + destruct sub as [ e | [ interface [ hkeyed sub ] ] ].
    - destruct e.
      assumption.
    - exists interface.
      exists hkeyed.
      eapply sic_sci; eassumption.
  + eapply sic_sci; eassumption.
  + destruct sub.
    simpl in sub'.
    assumption.
Qed.
Lemma sci_sic {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (concrete: GCConcrete core) (interface': scheme.(Interface)) (arguments': scheme.(IParameter) interface' -> GCType core) (concrete'': GCConcrete core): SubConcreteInterface history concrete interface' arguments' -> SubInterfaceConcrete history interface' arguments' concrete'' -> SubConcrete history concrete concrete''.
Proof.
  intros sub sub'.
  destruct concrete as [ listener | node | ]; simpl in *.
  + right.
    destruct sub as [ interface [ hkeyed sub ] ].
    exists interface.
    exists hkeyed.
    eapply si_sic; eassumption.
  + eapply si_sic; eassumption.
  + destruct sub.
Qed.
Lemma sci_si {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (concrete: GCConcrete core) (interface': scheme.(Interface)) (arguments': scheme.(IParameter) interface' -> GCType core) (interface'': scheme.(Interface)) (arguments'': scheme.(IParameter) interface'' -> GCType core): SubConcreteInterface history concrete interface' arguments' -> SubInterface history interface' arguments' interface'' arguments'' -> SubConcreteInterface history concrete interface'' arguments''.
Proof.
  intros sub sub'.
  destruct concrete as [ listener | node | ]; simpl in *.
  + destruct sub as [ interface [ hkeyed sub ] ].
    exists interface.
    exists hkeyed.
    eapply si_trans; eassumption.
  + eapply si_trans; eassumption.
  + destruct sub.
Qed.
Lemma sgct_trans' {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (type type' type'': GCType core): ConsistentGC history -> FinalGCHistory history -> SubGCType' history type type' -> SubGCType' history type' type'' -> SubGCType' history type type''.
Proof.
  intros consistent final sub sub'.
  destruct type as [ [ concrete | transitive ] | interface arguments ]; destruct type' as [ [ concrete' | transitive' ] | interface' arguments' ]; destruct type'' as [ [ concrete'' | transitive'' ] | interface'' arguments'' ]; simpl in *.
  + eapply sc_trans; eassumption.
  + destruct sub' as [ concrete'' sub' derived' ].
    exists concrete''; try assumption.
    eapply sc_trans; eassumption.
  + eapply sc_sci; eassumption.
  + destruct sub as [ concrete' sub derived ].
    destruct sub' as [ ? derived' sub' ].
    eapply sc_trans; try eassumption.
    eapply sc_trans; try eassumption.
    apply derived_sc; try assumption.
    apply dtransitive with transitive'; assumption.
  + destruct sub as [ concrete' sub derived ].
    destruct sub' as [ e | [ derived' | [ ? derived' [ concrete'' sub' derived'' ] ] ] ].
    - destruct e.
      exists concrete'; assumption.
    - exists concrete'; try assumption.
      eapply dtransitive; eassumption.
    - exists concrete''; try assumption.
      eapply sc_trans; try eassumption.
      eapply sc_trans; try eassumption.
      apply derived_sc; try assumption.
      eapply dtransitive; eassumption.
  + destruct sub as [ concrete' sub derived ].
    destruct sub' as [ concrete'' derived' sub' ].
    eapply sc_sci; try eassumption.
    eapply sc_sci; try eassumption.
    apply derived_sc; try assumption.
    eapply dtransitive; eassumption.
  + eapply sci_sic; eassumption.
  + destruct sub' as [ concrete' sub' derived' ].
    exists concrete'; try assumption.
    eapply sci_sic; eassumption.
  + eapply sci_si; eassumption.
  + destruct sub as [ concrete derived sub ].
    exists concrete; try assumption.
    eapply sc_trans; eassumption.
  + right.
    right.
    destruct sub as [ concrete derived sub ].
    destruct sub' as [ ? derived' sub' ].
    exists concrete; try assumption.
    eexists; try apply sub'.
    eapply sc_trans; eassumption.
  + destruct sub as [ concrete derived sub ].
    exists concrete; try assumption.
    eapply sc_sci; eassumption.
  + destruct sub' as [ concrete' derived'' sub' ].
    destruct sub as [ e | [ derived | [ concrete derived [ ? sub derived' ] ] ] ].
    - destruct e.
      exists concrete'; assumption.
    - exists concrete'; try assumption.
      eapply dtransitive; eassumption.
    - exists concrete; try assumption.
      eapply sc_trans; try eassumption.
      eapply sc_trans; try eassumption.
      apply derived_sc; try assumption.
      eapply dtransitive; eassumption.
  + destruct sub as [ e | [ derived | [ concrete derived [ ? sub ? ] ] ] ].
    - destruct e.
      assumption.
    - right.
      destruct sub' as [ e' | [ derived' | [ concrete' derived' [ ? sub' ? ] ] ] ].
      * left.
        destruct e'.
        assumption.
      * left.
        eapply dtransitive; eassumption.
      * right.
        exists concrete'.
        ** eapply dtransitive; eassumption.
        ** eexists; eassumption.
    - right.
      right.
      exists concrete; try eassumption.
      destruct sub' as [ e' | [ derived' | [ concrete' ? [ ? sub' derived' ] ] ] ].
      * destruct e'.
        eexists; eassumption.
      * eexists; try eassumption.
        eapply dtransitive; eassumption.
      * eexists; try apply derived'.
        eapply sc_trans; try eassumption.
        eapply sc_trans; try eassumption.
        apply derived_sc; try assumption.
        eapply dtransitive; eassumption.
  + destruct sub' as [ concrete' derived' sub' ].
    destruct sub as [ e | [ derived | [ concrete derived [ ? sub ? ] ] ] ].
    - destruct e.
      eexists; eassumption.
    - exists concrete'; try assumption.
      eapply dtransitive; eassumption.
    - exists concrete; try assumption.
      eapply sc_sci; try eassumption.
      eapply sc_sci; try eassumption.
      apply derived_sc; try assumption.
      eapply dtransitive; eassumption.
  + destruct sub as [ concrete derived sub ].
    exists concrete; try assumption.
    eapply sci_sic; eassumption.
  + right.
    right.
    destruct sub as [ concrete derived sub ].
    destruct sub' as [ concrete' sub' derived' ].
    exists concrete; try assumption.
    exists concrete'; try assumption.
    eapply sci_sic; eassumption.
  + destruct sub as [ concrete derived sub ].
    exists concrete; try assumption.
    eapply sci_si; eassumption.
  + eapply sic_sc; eassumption.
  + destruct sub' as [ concrete'' sub' derived' ].
    exists concrete''; try assumption.
    eapply sic_sc; eassumption.
  + eapply sic_sci; eassumption.
  + destruct sub as [ concrete sub derived ].
    destruct sub' as [ concrete' derived' sub' ].
    eapply sic_sc; try eassumption.
    eapply sc_trans; try eassumption.
    apply derived_sc; try assumption.
    eapply dtransitive; eassumption.
  + destruct sub as [ concrete' sub derived ].
    destruct sub' as [ e' | [ derived' | [ ? derived' [ concrete'' sub' derived'' ] ] ] ].
    - destruct e'.
      exists concrete'; assumption.
    - exists concrete'; try assumption.
      eapply dtransitive; eassumption.
    - exists concrete''; try assumption.
      eapply sic_sc; try eassumption.
      eapply sc_trans; try eassumption.
      apply derived_sc; try assumption.
      eapply dtransitive; eassumption.
  + destruct sub as [ concrete sub derived ].
    destruct sub' as [ concrete' derived' sub' ].
    eapply sic_sci; try eassumption.
    eapply sc_sci; try eassumption.
    apply derived_sc; try assumption.
    eapply dtransitive; eassumption.
  + eapply si_sic; eassumption.
  + destruct sub' as [ concrete' sub' derived' ].
    exists concrete'; try assumption.
    eapply si_sic; eassumption.
  + eapply si_trans; eassumption.
Qed.

(* The above ensure coalgebraic subtyping has the required algebraic structure, so by induction we know it is implied by inductive subtyping. *)
Lemma sgct_sgct' {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} (history: GCHistory core) (type type': GCType core): ConsistentGC history -> FinalGCHistory history -> SubGCType history type type' -> SubGCType' history type type'.
Proof.
  intros consistent final sub.
  induction sub; simpl.
  + apply sgct_refl'.
  + eapply sgct_trans'; eassumption.
  + apply sivariance.
    intro parameter.
    apply isigned_signed.
    auto.
  + constructor.
  + destruct atom as [ concrete | transitive ]; destruct atom' as [ concrete' | transitive' ].
    - apply derived_sc; assumption.
    - eexists; try eassumption.
      apply sc_refl.
    - eexists; try eassumption.
      apply sc_refl.
    - right.
      left.
      assumption.
  + apply si_refl.
  + apply si_refl.
  + eexists.
    eexists.
    apply si_refl.
Qed.



(* Part 8.2: Graphical-Core Consistency ensures Type-Space Consistency
 * Here we prove Lemma 9.5 of the paper, that if a graphical core is consistent using some history then so is its type space with that history.
 *)

Lemma gcur_consistent
      {Interface_SSet: SSet scheme.(Interface)}
      {Transitive: Sort}
      (core: GraphicalCore Transitive)
      (history: GCHistory core)
      (type: GCType core)
    : ConsistentGC history
   -> FinalGCHistory history
   -> UnReachableGC history type
   -> existsTSS listener: GCNListener core, SubGCType' history type (gctatom (gcaconcrete (gcclistener listener))) & GCNHUnResolvedS history listener.
Proof.
  intros consistent final ur.
  induction ur as [ type type' sub _ IHur | listener ur ].
  + destruct IHur as [ listener sub' IHur ].
    exists listener; try assumption.
    eapply sgct_trans'; try eassumption.
    apply sgct_sgct'; assumption.
  + exists listener; try assumption.
    simpl.
    left.
    reflexivity.
Qed.

Lemma consistent_gc_ts
      {Interface_SSet: SSet scheme.(Interface)}
      {Transitive: Sort}
      (core: GraphicalCore Transitive)
      (history: GCHistory core)
    : ConsistentGC history
   -> FinalGCHistory history
   -> ConsistentTypeSpace (GCTypeSpace history).
Proof.
  intros consistent final.
  constructor; simpl.
  + intros interface arguments interface' arguments' sub.
    apply sgct_sgct' in sub; try assumption; simpl in sub.
    destruct sub as [ arguments' sub ].
    exists (eqS_refl interface).
    rewrite convert_id.
    assumption.
  + intro ur.
    apply gcur_consistent in ur; try assumption.
    destruct ur as [ listener' sub _ ].
    simpl in sub.
    apply eqS_squash_eq in sub.
    destruct sub as [ sub ].
    discriminate sub.
  + intros interface arguments sub.
    apply sgct_sgct' in sub; assumption.
  + intros interface arguments ur.
    apply gcur_consistent in ur; try assumption.
    destruct ur as [ listener' sub ur' ].
    simpl in sub.
    destruct sub as [ node _ derived ].
    apply consistent in derived.
    eapply fgcnhunresolved in ur'; eassumption.
Qed.



(* Part 8.3: Model Extension
 * Given a model of a graphical core, we can extend the model to the nested components of the graphical core.
 *)

Definition mntransitive: forall {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (transitive: GCNTransitive core), GCNTActivatedS history transitive -> space.(SpaceType)
:= fix mntransitive {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (transitive: GCNTransitive core): GCNTActivatedS history transitive -> space.(SpaceType)
:= match transitive with
   | gcntabstract abstract => fun _ => model.(mabstract) abstract
   | gcntargument listener interface keyed parameter => fun activated => model.(mlargument) listener interface activated parameter
   | gcntnested listener interface keyed transitive => fun activated => mntransitive (model.(mlaction) listener interface activated.(proj1_exSS)) transitive activated.(proj2_exSS)
   end.
Definition mnnode: forall {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (node: GCNNode core), GCNNActivatedS history node -> space.(SpaceType)
:= fix mnnode {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (node: GCNNode core): GCNNActivatedS history node -> space.(SpaceType)
:= match node with
   | gcnnnode node => fun _ => model.(mnode) node
   | gcnnnested listener interface keyed node => fun activated => mnnode (model.(mlaction) listener interface activated.(proj1_exSS)) node activated.(proj2_exSS)
   end.
Definition mnlistener: forall {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (listener: GCNListener core), GCNLActivatedS history listener -> space.(SpaceType)
:= fix mnlistener {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (listener: GCNListener core): GCNLActivatedS history listener -> space.(SpaceType)
:= match listener with
   | gcnllistener listener => fun _ => model.(mlistener) listener
   | gcnlnested listener interface keyed listener' => fun activated' => mnlistener (model.(mlaction) listener interface activated'.(proj1_exSS)) listener' activated'.(proj2_exSS)
   end.
Definition mconcrete {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (concrete: GCConcrete core): GCCActivatedS history concrete -> space.(SpaceType)
:= match concrete with
   | gcclistener listener => mnlistener model listener
   | gccnode node => mnnode model node
   | gccany => fun _ => space.(stany)
   end.
Definition mtransitive {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (elimination: SortElimination space.(SpaceType) Transitive) (transitive: GCTransitive core): GCTActivatedS history transitive -> space.(SpaceType)
:= match transitive with
   | gctntransitive transitive => mntransitive model transitive
   | gcttransitive transitive => fun _ => apply_elimination elimination transitive
   end.
Definition matom {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (elimination: SortElimination space.(SpaceType) Transitive) (atom: GCAtom core): GCAActivatedS history atom -> space.(SpaceType)
:= match atom with
   | gcaconcrete concrete => mconcrete model concrete
   | gcatransitive transitive => mtransitive model elimination transitive
   end.
Lemma mnlowerv {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (node: GCNNode core) (activated: GCNNActivatedS history node) (elimination: SortElimination space.(SpaceType) Transitive): ModelV model elimination -> space.(SubSpaceType) (space.(stinterface) (gcnninterface node) (fun parameter => matom model elimination (apply_elimination (gcatomize core) (gcnnargument node parameter)) (gcnnargument_activated node parameter activated))) (mnnode model node activated).
Proof.
  intro vmodel.
  induction node; simpl.
  + eapply space.(ssttrans); try apply vmodel.(mlowerv).
    apply space.(sstvariance).
    intro parameter.
    unfold meliminate.
    unfold melimination.
    generalize (gcnnargument_activated (gcnnnode node) parameter activated).
    simpl.
    rewrite <- apply_eliminate_morphism.
    unfold gcatomize.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_id_morphism.
    destruct (core.(gcnargument) node parameter) as [ [] | [ node' | [ transitive | transitive ] ] ]; simpl; try (intro; apply signed_refl; apply space.(sstrefl)).
    rewrite apply_compose_elimination.
    rewrite apply_eliminate_sum.
    simpl.
    intros _.
    apply signed_refl.
    apply space.(sstrefl).
  + eapply space.(ssttrans); try (apply IHnode; apply (vmodel.(mlactionv) listener interface activated.(proj1_exSS))); clear IHnode.
    apply space.(sstvariance).
    intro parameter.
    generalize (gcnnargument_activated (gcnnnested listener interface keyed node) parameter activated).
    destruct activated as [ hkeyed activated ].
    cbn.
    generalize (gcnnargument_activated node parameter activated).
    clear activated.
    unfold gcatomize.
    simpl.
    rewrite <- apply_eliminate_morphism.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_pair_morphism.
    rewrite eliminate_select_head_pair_elimination.
    rewrite eliminate_pair_morphism.
    rewrite eliminate_select_head_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_id_morphism.
    destruct (gcnnargument node parameter) as [ [] | [ node' | [ transitive | [ parameter' | [ abstract | transitive ] ] ] ] ]; simpl in *; try (intros; apply signed_refl; apply space.(sstrefl)).
    rewrite apply_compose_elimination.
    rewrite apply_eliminate_sum.
    rewrite apply_compose_elimination.
    rewrite apply_eliminate_sum.
    simpl.
    intros _ _.
    apply signed_refl.
    apply space.(sstrefl).
Qed.
Lemma mnupperv {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (node: GCNNode core) (activated: GCNNActivatedS history node) (elimination: SortElimination space.(SpaceType) Transitive): ModelV model elimination -> space.(SubSpaceType) (mnnode model node activated) (space.(stinterface) (gcnninterface node) (fun parameter => matom model elimination (apply_elimination (gcatomize core) (gcnnargument node parameter)) (gcnnargument_activated node parameter activated))).
Proof.
  intro vmodel.
  induction node; simpl.
  + eapply space.(ssttrans); try apply vmodel.(mupperv).
    apply space.(sstvariance).
    intro parameter.
    unfold meliminate.
    unfold melimination.
    generalize (gcnnargument_activated (gcnnnode node) parameter activated).
    simpl.
    rewrite <- apply_eliminate_morphism.
    unfold gcatomize.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_id_morphism.
    destruct (core.(gcnargument) node parameter) as [ [] | [ node' | [ transitive | transitive ] ] ]; simpl; try (intro; apply signed_refl; apply space.(sstrefl)).
    rewrite apply_compose_elimination.
    rewrite apply_eliminate_sum.
    simpl.
    intros _.
    apply signed_refl.
    apply space.(sstrefl).
  + eapply space.(ssttrans); try (apply IHnode; apply (vmodel.(mlactionv) listener interface activated.(proj1_exSS))); clear IHnode.
    apply space.(sstvariance).
    intro parameter.
    generalize (gcnnargument_activated (gcnnnested listener interface keyed node) parameter activated).
    destruct activated as [ hkeyed activated ].
    cbn.
    generalize (gcnnargument_activated node parameter activated).
    clear activated.
    unfold gcatomize.
    simpl.
    rewrite <- apply_eliminate_morphism.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_pair_morphism.
    rewrite eliminate_select_head_pair_elimination.
    rewrite eliminate_pair_morphism.
    rewrite eliminate_select_head_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_id_morphism.
    destruct (gcnnargument node parameter) as [ [] | [ node' | [ transitive | [ parameter' | [ abstract | transitive ] ] ] ] ]; simpl in *; try (intros; apply signed_refl; apply space.(sstrefl)).
    rewrite apply_compose_elimination.
    rewrite apply_eliminate_sum.
    rewrite apply_compose_elimination.
    rewrite apply_eliminate_sum.
    simpl.
    intros _ _.
    apply signed_refl.
    apply space.(sstrefl).
Qed.
Lemma mnlargumentv {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (listener: GCNListener core) (interface: scheme.(Interface)) (hkeyed: GCNHKeyedS history listener interface) (elimination: SortElimination space.(SpaceType) Transitive): ModelV model elimination -> space.(SubSpaceType) (mnlistener model listener (gcnlactivatedS hkeyed)) (space.(stinterface) interface (fun parameter => mntransitive model (gcntlargument listener interface (gcnhkeyed hkeyed) parameter) (gcntlargument_activated listener interface hkeyed parameter (gcnlactivatedS hkeyed)))).
Proof.
  intro vmodel.
  induction listener as [ Transitive core listener | Transitive core listener' interface' keyed' listener ]; simpl.
  + apply vmodel.(mlargumentv) with (hkeyed := hkeyed).
  + simpl in hkeyed.
    destruct hkeyed as [ hkeyed' hkeyed ].
    specialize (IHlistener (history.(gchaction) listener' interface' hkeyed') (model.(mlaction) listener' interface' hkeyed') hkeyed (pair_elimination (model.(mlargument) listener' interface' hkeyed') (pair_elimination model.(mabstract) elimination)) (vmodel.(mlactionv) listener' interface' hkeyed')).
    apply IHlistener.
Qed.
Lemma mnunresolvedv {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (listener: GCNListener core) (ur: GCNHUnResolvedS history listener) (elimination: SortElimination space.(SpaceType) Transitive): ModelV model elimination -> space.(UnReachable) (mnlistener model listener (gcnlactivatedS' ur)).
Proof.
  intro vmodel.
  induction listener as [ Transitive core listener | Transitive core listener' interface' keyed' listener ]; simpl.
  + apply vmodel.(munresolvedv).
    assumption.
  + simpl in ur.
    destruct ur as [ hkeyed ur ].
    specialize (IHlistener (history.(gchaction) listener' interface' hkeyed) (model.(mlaction) listener' interface' hkeyed) ur (pair_elimination (model.(mlargument) listener' interface' hkeyed) (pair_elimination model.(mabstract) elimination)) (vmodel.(mlactionv) listener' interface' hkeyed)).
    apply IHlistener.
Qed.
Lemma mnconstraintv {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (elimination: SortElimination space.(SpaceType) Transitive) (constraint: GCNConstraint core): ModelV model elimination -> forall activated: GCNCActivatedS history constraint, space.(SubSpaceType) (matom model elimination (gcaclower constraint) (constraint_activated activated).(proj1_AndS)) (matom model elimination (gcacupper constraint) (constraint_activated activated).(proj2_AndS)).
Proof.
  intros vmodel activated.
  generalize (constraint_activated activated).(proj1_AndS).
  generalize (constraint_activated activated).(proj2_AndS).
  unfold gcacupper.
  unfold gcatomizel.
  unfold gcaclower.
  unfold gcatomize.
  induction constraint; simpl in *.
  + clear activated.
    rewrite <- apply_eliminate_morphism.
    rewrite <- apply_eliminate_morphism.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_id_morphism.
    generalize (vmodel.(mconstraintv) constraint).
    destruct (core.(gcclower) constraint) as [ [] | [ node | [ transitive | transitive ] ] ]; destruct (core.(gccupper) constraint) as [ listener' | [ [] | [ node' | [ transitive' | transitive' ] ] ] ]; repeat (simpl; unfold compose; try rewrite apply_compose_elimination; try rewrite apply_eliminate_sum); auto.
  + destruct activated as [ hkeyed activated ].
    specialize (IHconstraint (history.(gchaction) listener interface hkeyed) _ _ (vmodel.(mlactionv) listener interface hkeyed) activated).
    rewrite <- apply_eliminate_morphism.
    rewrite <- apply_eliminate_morphism.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_pair_morphism.
    rewrite eliminate_select_head_pair_elimination.
    rewrite eliminate_pair_morphism.
    rewrite eliminate_select_head_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_id_morphism.
    revert IHconstraint.
    destruct (gcnclower constraint) as [ [] | [ node | [ transitive | [ parameter | [ abstract | transitive ] ] ] ] ]; destruct (gcncupper constraint) as [ listener' | [ [] | [ node' | [ transitive' | [ parameter' | [ abstract' | transitive' ] ] ] ] ] ]; repeat (simpl; unfold compose; try rewrite apply_compose_elimination; try rewrite apply_eliminate_sum); try auto; try (intros ? ? [ ? ? ] || intros ? [ ? ? ]); cbn; auto using trueS.
Qed.
Lemma msderivedv {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (elimination: SortElimination space.(SpaceType) Transitive) (atom atom': GCAtom core): ConsistentTypeSpace space -> ModelV model elimination -> forall sign: Sign, forall derived: SDerived history sign atom atom', Signed space.(SubSpaceType) sign (matom model elimination atom (sderived_activated derived).(proj1_AndS)) (matom model elimination atom' (sderived_activated derived).(proj2_AndS)).
Proof.
  intros consistent vmodel.
  intros sign derived.
  induction derived; simpl in *.
  + assumption.
  + apply (mnconstraintv model elimination constraint vmodel activated).
  + eapply space.(ssttrans); eassumption.
  + simpl in *.
    assert (space.(SubSpaceType) (space.(stinterface) (gcnninterface node) (fun parameter => matom model elimination (apply_elimination (gcatomize core) (gcnnargument node parameter)) (gcnnargument_activated _ _ (sderived_activated derived).(proj1_AndS)))) (space.(stinterface) (gcnninterface node') (fun parameter' => matom model elimination (apply_elimination (gcatomize core) (gcnnargument node' parameter')) (gcnnargument_activated _ _ (sderived_activated derived).(proj2_AndS))))) as sub.
    - eapply space.(ssttrans); try (apply mnlowerv; assumption).
      eapply space.(ssttrans); try (apply mnupperv; assumption).
      assumption.
    - apply consistent.(ctsinterface) in sub.
      destruct sub as [ e' sub ].
      merge e e'.
      apply sub.
  + simpl in *.
    assert (space.(SubSpaceType) (space.(stinterface) (gcnninterface node) (fun parameter => matom model elimination (apply_elimination (gcatomize core) (gcnnargument node parameter)) (gcnnargument_activated _ _ (sderived_activated derived).(proj1_AndS)))) (space.(stinterface) interface' (fun parameter' => mntransitive model (gcntlargument listener' interface' (gcnhkeyed hkeyed') parameter') (gcntlargument_activated _ _ hkeyed' _ (sderived_activated derived).(proj2_AndS))))) as sub.
    - eapply space.(ssttrans); try (apply mnlowerv; assumption).
      eapply space.(ssttrans); try (eapply mnlargumentv with (hkeyed := hkeyed'); eassumption).
      assumption.
    - apply consistent.(ctsinterface) in sub.
      destruct sub as [ e' sub ].
      merge e e'.
      apply sub.
Qed.
Lemma mderivedv {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (elimination: SortElimination space.(SpaceType) Transitive) (atom atom': GCAtom core): ConsistentTypeSpace space -> ModelV model elimination -> forall derived: Derived history atom atom', existsSS activated: GCAActivatedS history atom, existsSS activated': GCAActivatedS history atom', space.(SubSpaceType) (matom model elimination atom activated) (matom model elimination atom' activated').
Proof.
  intros consistent vmodel derived.
  eexists.
  eexists.
  eapply msderivedv with (derived := derived); assumption.
Qed.



(* Part 8.4: Model Consistency implies Graphical-Core Consistency
 * Here we prove Lemma 9.6 of the paper, that for any type space modeling a graphical core, if that type space is consistent then so is the graphical core.
 * Note that the model does not need to be the canonical model given by the graphical core's type space.
 *)
Lemma consistent_ts_gc
      {Interface_SSet: SSet scheme.(Interface)}
      {Transitive: Sort}
      (core: GraphicalCore Transitive)
      (history: GCHistory core)
      (space: TypeSpace)
      (model: Model history space)
      (elimination: SortElimination space.(SpaceType) Transitive)
    : ModelV model elimination
   -> ConsistentTypeSpace space
   -> FinalGCHistory history
   -> ConsistentGC history.
Proof.
  intros vmodel consistent final.
  intros atom atom' derived.
  pose proof derived as sub.
  eapply mderivedv in sub; try eassumption.
  destruct sub as [ activated [ activated' sub ] ].
  destruct atom as [ concrete | transitive ]; destruct atom' as [ concrete' | transitive' ]; simpl; try constructor.
  destruct concrete as [ listener | node | ]; [ destruct concrete'; apply derived_listener_false in derived; destruct derived | | ]; destruct concrete' as [ listener' | node' | ]; simpl in *; try constructor.
  + eapply space.(ssttrans) in sub; [ | apply mnlowerv; try eassumption ].
    pose proof activated' as res'.
    apply fgcnhresolved in res'; try assumption.
    destruct res' as [ ur | [ interface' hkeyed' ] ]; try assumption.
    - edestruct consistent.(ctsinterfaceunreachable).
      eapply space.(sstur); try eapply mnunresolvedv with (ur := ur); eassumption.
    - eapply (fun left right => space.(ssttrans) _ _ _ right left) in sub; [ | eapply mnlargumentv with (hkeyed := hkeyed'); eassumption ].
      apply consistent.(ctsinterface) in sub.
      destruct sub as [ e _ ].
      destruct e.
      assumption.
  + edestruct consistent.(ctsinterface) as [ e _ ]; simpl.
    - eapply space.(ssttrans); [ eapply mnlowerv; eassumption | ].
      eapply space.(ssttrans); [ | eapply mnupperv; eassumption ].
      eassumption.
    - assumption.
  + destruct (fgcnhresolved (history := history)) with listener' as [ ur | [ interface hkeyed ] ]; try assumption.
    - eapply consistent.(ctsanyunreachable).
      simpl.
      eapply space.(sstur); try eapply mnunresolvedv with (ur := ur); eassumption.
    - eapply consistent.(ctsanyinterface).
      simpl.
      eapply space.(ssttrans); try eapply mnlargumentv with (hkeyed := hkeyed); eassumption.
  + eapply consistent.(ctsanyinterface).
    simpl.
    eapply space.(ssttrans); try eapply mnupperv; eassumption.
Qed.



(* Part 9: Configurations
 * Here we specialize various concepts to finite graphical histories.
 * For example, like in Definition 8.2 of the paper, we can define configurations of a graphical core using partial finite maps from its label-listeners once we know that set of label-listeners is subfinite (and therefore subcountable).
 *)

(* Part 9.1: Finite Graphical Cores
 * For most components, we only need to know subfiniteness (or decidability) to ensure termination.
 * Only for constraints do we need true finiteness, since we need to be able to enumerate through all of the constraints.
 * Note, furthermore, that FiniteGraphicalCore is defined inductively rather than coinductively.
 * This well-foundedness ensures that elaborating the nested graphical cores triggered by resolving nested label-listeners eventually terminates.
 * In particular, this is how the inductive structure of the expression of the source program gets captured as an inductive structure on the graphical core in order to prove termination.
 *)
#[projections(primitive=no)]
Inductive FiniteGraphicalCore {Transitive: Sort} {core: GraphicalCore Transitive}: Type :=
{ GCAbstract_SubFinite: SubFinite core.(GCAbstract);
  GCNode_SubFinite: SubFinite core.(GCNode);
  GCListener_SubFinite: SubFinite core.(GCListener);
  GCConstraint_Finite: Finite core.(GCConstraint);
  GCLKeyedS_DecidableS (listener: core.(GCListener)) (interface: scheme.(Interface)): DecidableS (core.(GCLKeyedS) listener interface);
  gclaction_Finite (listener: core.(GCListener)) (interface: scheme.(Interface)) (keyed: core.(GCLKeyedS) listener interface): FiniteGraphicalCore (core := core.(gclaction) listener interface keyed);
}.
Arguments FiniteGraphicalCore {_} _.
Existing Class FiniteGraphicalCore.
#[local] Existing Instance GCAbstract_SubFinite.
#[local] Existing Instance GCNode_SubFinite.
#[local] Existing Instance GCListener_SubFinite.
#[local] Existing Instance GCConstraint_Finite.
#[local] Existing Instance GCLKeyedS_DecidableS.
#[local] Existing Instance gclaction_Finite.

#[local] Instance GCNLKeyedS_DecidableS {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (listener: GCNListener core) (interface: scheme.(Interface)): DecidableS (GCNLKeyedS listener interface).
Proof.
  induction listener as [ Transitive core listener | Transitive core listener interface' keyed' listener' IHlistener' ]; simpl.
  + apply _.
  + apply IHlistener'.
    apply _.
Qed.

#[local] Instance gcmap_Finite {Transitive Transitive'} (tmap: SortMorphism Transitive Transitive') (core: GraphicalCore Transitive) {core_Finite: FiniteGraphicalCore core}: FiniteGraphicalCore (gcmap tmap core).
Proof.
  revert Transitive' tmap; induction core_Finite as [ Transitive core gca_SubFinite gcn_SubFinite gcl_SubFinite gcc_Finite gclk_Decidable gcla_Finite IHcore ]; intros Transitive' tmap.
  constructor; cbn; apply _.
Qed.


(* Part 9.2: Configurations
 * A configuration is the particular implementation of a history used by our algorithm.
 * It uses partial maps to track which label-listeners have been resolved to which interfaces.
 *)

Record CEntry' {Configuration: forall {Transitive: Sort} (core: GraphicalCore Transitive) `{FiniteGraphicalCore Transitive core}, Type} {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} {listener: core.(GCListener)}: Type :=
{ ceinterface: scheme.(Interface);
  cekeyed: core.(GCLKeyedS) listener ceinterface;
  ceconfiguration: Configuration (core.(gclaction) listener ceinterface cekeyed)
}.
Arguments CEntry' _ {_} _ {_} _.
CoInductive Configuration {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core}: Type :=
{ cmap: SCMap core.(GCListener) (CEntry' (@Configuration) core);
}.
Arguments Configuration {_} _ {_}.
Definition CEntry: forall {Transitive: Sort} (core: GraphicalCore Transitive) `{FiniteGraphicalCore Transitive core}, core.(GCListener) -> Type
:= @CEntry' (@Configuration).

Definition configuration_empty {Transitive: Sort} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core}: Configuration core :=
{| cmap := scmempty |}.

(* chistory specifies the history that a configuration represents. *)
Definition chistory `{SSet scheme.(Interface)}: forall {Transitive: Sort} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (configuration: Configuration core), GCHistory core
:= cofix chistory {Transitive: Sort} (core: GraphicalCore Transitive) `{FiniteGraphicalCore Transitive core} (configuration: Configuration core): GCHistory core :=
{| GCHKeyedS listener interface := existsSS contains: SCMapContains configuration.(cmap) listener, eqS (scmget_contained configuration.(cmap) listener contains).(ceinterface) interface;
   GCHUnResolvedS listener := SCMapContains configuration.(cmap) listener -> FalseS;
   gchkeyed listener interface hkeyed := convertS hkeyed.(proj2_exSS) (core.(GCLKeyedS) listener) (scmget_contained configuration.(cmap) listener hkeyed.(proj1_exSS)).(cekeyed);
   gchaction listener interface hkeyed := chistory (core.(gclaction) listener interface _) (convert hkeyed.(proj2_exSS) (fun interface => forall keyed: core.(GCLKeyedS) listener interface, Configuration (core.(gclaction) listener interface keyed)) (fun _ => (scmget_contained configuration.(cmap) listener hkeyed.(proj1_exSS)).(ceconfiguration)) _);
|}.

Lemma chistory_final {Interface_SSet: SSet scheme.(Interface)}: forall {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core), FinalGCHistory (chistory configuration).
Proof.
  cofix chistory_final.
  intros Transitive core core_Finite configuration.
  constructor; cbn.
  + intros listener interface interface' [ contains e ] [ contains' e' ].
    destruct e.
    destruct e'.
    reflexivity.
  + intros listener ncontains interface [ contains _ ].
    apply ncontains.
    assumption.
  + intro listener.
    destruct (decidableS (SCMapContains configuration.(cmap) listener)) as [ contains | ncontains ].
    - right.
      exists (scmget_contained configuration.(cmap) listener contains).(ceinterface).
      exists contains.
      reflexivity.
    - left.
      assumption.
  + intros listener interface [ contains e ].
    destruct e.
    cbn.
    rewrite convert_id.
    apply chistory_final.
Qed.

Lemma chkeyed_empty {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core}: forall {listener: GCNListener core}, forall {interface: scheme.(Interface)}, GCNHKeyedS (chistory configuration_empty) listener interface -> FalseS.
Proof.
  intros listener interface hkeyed.
  destruct listener as [ listener | listener interface' keyed' listener' ]; cbn in hkeyed.
  + destruct hkeyed as [ [ ] _ ].
  + destruct hkeyed as [ [ [ ] _ ] _ ].
Qed.

(* configuration_set is the key function for conceptually mutating a configuration.
 * One provides it with a configuration, an activated nested label-listener, and an interface to resolve that label-listener to.
 * Then it either returns the corresponding updated configuration, or an indication that the label-listener is already resolved that that interface, or an indication that the label-listener is already resolved to a distinct interface.
 *)
Definition configuration_set {Interface_DecEq: DecEq scheme.(Interface)}: forall {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (listener: GCNListener core), GCNLActivatedS (chistory configuration) listener -> forall interface: scheme.(Interface), GCNLKeyedS listener interface -> option (option (Configuration core))
:= fix configuration_set (Transitive: Sort) (core: GraphicalCore Transitive) {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (listener: GCNListener core) {struct listener}: GCNLActivatedS (chistory configuration) listener -> forall interface: scheme.(Interface), GCNLKeyedS listener interface -> option (option (Configuration core))
:= match listener as listener return GCNLActivatedS (chistory configuration) listener -> forall interface: scheme.(Interface), GCNLKeyedS listener interface -> option (option (Configuration core)) with
   | gcnllistener listener => fun activated interface keyed => option_map (option_map (fun map => {| cmap := map |})) (scmupdate configuration.(cmap) listener (fun entry => match entry with
                                                                                                                                                                             | sbleftS contains => match (decidableS (eqS interface (scmget_contained configuration.(cmap) listener contains).(ceinterface))) with
                                                                                                                                                                                                   | sbleftS _ => Some None
                                                                                                                                                                                                   | sbrightS _ => None
                                                                                                                                                                                                  end
                                                                                                                                                                             | sbrightS _ => Some (Some {| ceinterface := interface; cekeyed := keyed; ceconfiguration := configuration_empty |})
                                                                                                                                                                             end))
   | gcnlnested listener interface keyed listener' => fun activated interface' keyed' => option_map (option_map (fun map => {| cmap := map |})) (scmupdate configuration.(cmap) listener (fun entry => match entry with
                                                                                                                                                                                                       | sbleftS contains => option_map (option_map (fun entry => {| ceinterface := interface; cekeyed := keyed; ceconfiguration := entry |})) (configuration_set (cons (scheme.(IParameter) interface) (cons core.(GCAbstract) Transitive)) (core.(gclaction) listener interface keyed) (convert activated.(proj1_exSS).(proj2_exSS) (fun interface => forall keyed, Configuration (Transitive := cons (scheme.(IParameter) interface) (cons core.(GCAbstract) Transitive)) (core.(gclaction) listener interface keyed)) (fun _ => (scmget_contained configuration.(cmap) listener contains).(ceconfiguration)) _) listener' activated.(proj2_exSS) interface' keyed')
                                                                                                                                                                                                       | sbrightS _ => Some None
                                                                                                                                                                                                       end))
   end.

(* CExtends is a non-strict property because it is often used for termination, and Rocq can only structurally recurse on non-strict propositions.
 * It indicates that the latter configuration is the former configuration strictly extended with the given activated label-listener resolved to the given interface.
 *)
Definition CExtends `{SSet scheme.(Interface)}: forall {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (listener: GCNListener core) (activated: GCNLActivatedS (chistory configuration) listener) (interface: scheme.(Interface)) (configuration': Configuration core), Prop
:= fix CExtends {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (listener: GCNListener core) {struct listener}: GCNLActivatedS (chistory configuration) listener -> scheme.(Interface) -> Configuration core -> Prop
:= match listener with
   | gcnllistener listener => fun _ interface configuration' => (SCMapContains configuration.(cmap) listener -> False)
                                                             /\ exists2 entry: CEntry core listener,
                                                                SCMExtends configuration.(cmap) listener entry configuration'.(cmap)
                                                              & entry.(ceinterface) = interface
                                                             /\ entry.(ceconfiguration) = configuration_empty
   | gcnlnested listener interface keyed listener' => fun activated interface' configuration' => exists2 entry: CEntry core listener,
                                                                                                 SCMExtends configuration.(cmap) listener entry configuration'.(cmap)
                                                                                               & existsSP e: eqS entry.(ceinterface) interface,
                                                                                                 CExtends (core := core.(gclaction) listener interface keyed) (convert activated.(proj1_exSS).(proj2_exSS) (fun interface => forall keyed: core.(GCLKeyedS) listener interface, Configuration (core.(gclaction) listener interface keyed)) (fun _ => (scmget_contained configuration.(cmap) listener activated.(proj1_exSS).(proj1_exSS)).(ceconfiguration)) _) listener' activated.(proj2_exSS) interface' (convert e (fun interface => forall keyed: core.(GCLKeyedS) listener interface, Configuration (core.(gclaction) listener interface keyed)) (fun _ => entry.(ceconfiguration)) _)
   end.

(* This lemma is what enables us to iteratively refine the configuration and yet still be guaranteed to terminate. *)
Lemma ssc_cwf {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core): CoAcc (fun configuration configuration' => exists listener: GCNListener core, existsSP activated: GCNLActivatedS (chistory configuration) listener, exists interface: scheme.(Interface), CExtends configuration listener activated interface configuration') configuration.
Proof.
  induction core_Finite as [ Transitive core gca_SubFinite gcn_SubFinite gcl_SubFinite gcc_Finite gclk_Decidable gcla_Finite IHcore ].
  set (core_Finite := {| GCAbstract_SubFinite := gca_SubFinite |}).
  generalize (eq_refl configuration.(cmap)).
  generalize (sfmap_cwf (fun listener entry entry' => existsSP e: eqS entry.(ceinterface) entry'.(ceinterface), exists listener', existsSP activated', exists interface', CExtends (convert e (fun interface => forall keyed: core.(GCLKeyedS) listener interface, Configuration (core.(gclaction) listener interface keyed) (core_Finite := gcla_Finite listener interface keyed)) (fun _ => entry.(ceconfiguration)) _) listener' activated' interface' (entry'.(ceconfiguration))) configuration.(cmap)).
  generalize configuration.(cmap) at 1 3.
  intros map map_cwf.
  revert configuration.
  induction map_cwf as [ map _ IHmap ].
  + intros configuration e.
    destruct e.
    constructor.
    intros configuration' [ listener [ activated [ interface' extends ] ] ].
    eapply IHmap; try reflexivity.
    destruct listener as [ listener | listener interface keyed listener' ]; simpl in *.
    - exists listener.
      destruct extends as [ ncontains [ entry extends e ] ].
      exists entry; try assumption.
      intro contains.
      exfalso.
      apply ncontains.
      assumption.
    - exists listener.
      destruct extends as [ entry extends [ e extends' ] ].
      exists entry; try assumption.
      intro contains.
      destruct (eqS_eq e); rewrite convert_id in extends'; clear e.
      destruct activated as [ [ contains' e ] activated' ].
      merge contains contains'.
      cbn in *.
      exists e.
      exists listener'.
      exists activated'.
      exists interface'.
      assumption.
  + clear map.
    intros listener entry.
    assert (convert (eqS_refl entry.(ceinterface)) (fun interface => forall keyed, Configuration (core.(gclaction) listener interface keyed)) (fun _ => entry.(ceconfiguration)) _ = entry.(ceconfiguration)) as econfiguration by (rewrite convert_id; reflexivity).
    revert econfiguration.
    generalize entry.(ceconfiguration) at 2.
    generalize entry.(cekeyed).
    generalize (eqS_refl entry.(ceinterface)).
    generalize entry.(ceinterface) at 2 3 4 5 6 7 8 9 11.
    intros interface einterface keyed configuration econfiguration.
    specialize (IHcore listener interface keyed configuration).
    revert entry einterface econfiguration; induction IHcore as [ configuration _ IHconfiguration ]; intros entry einterface econfiguration.
    destruct (eqS_eq einterface); rewrite convert_id in econfiguration; clear einterface.
    destruct econfiguration.
    constructor.
    intros entry' [ e extends ].
    destruct entry' as [ interface' keyed' configuration' ].
    cbn in *.
    destruct (eqS_eq e); rewrite convert_id in extends; clear e.
    merge keyed keyed'.
    specialize (IHconfiguration configuration' extends {| ceinterface := entry.(ceinterface); cekeyed := keyed; ceconfiguration := configuration' |} (eqS_refl _)).
    rewrite convert_id in IHconfiguration.
    specialize (IHconfiguration eq_refl).
    assumption.
Qed.

Lemma configuration_set_extends
      {Interface_DecEq: DecEq scheme.(Interface)}
      {Transitive: Sort}
      {core: GraphicalCore Transitive}
      {core_Finite: FiniteGraphicalCore core}
      (configuration: Configuration core)
      (listener: GCNListener core)
      (activated: GCNLActivatedS (chistory configuration) listener)
      (interface: scheme.(Interface))
      (keyed: GCNLKeyedS listener interface)
    : match configuration_set configuration listener activated interface keyed with
      | None => exists2 interface': scheme.(Interface),
                Box (GCNHKeyedS (chistory configuration) listener interface')
              & interface = interface' -> False
      | Some None => Box (GCNHKeyedS (chistory configuration) listener interface)
      | Some (Some configuration') => CExtends configuration listener activated interface configuration'
      end.
Proof.
  induction listener as [ Transitive core listener | Transitive core listener interface' keyed' listener' IHlistener' ]; simpl in *.
  + match goal with |- match option_map (option_map _) (scmupdate _ _ ?update) with _ => _ end => pose proof (scmupdate_extends configuration.(cmap) listener update) as extends end.
    specialize (extends (fun entry => entry.(ceinterface) = interface /\ entry.(ceconfiguration) = configuration_empty)).
    specialize (extends (fun contains => (scmget_contained configuration.(cmap) listener contains).(ceinterface) = interface -> False)).
    specialize (extends (fun contains => (scmget_contained configuration.(cmap) listener contains).(ceinterface) = interface)).
    specialize (extends (fun contains entry' => False)).
    match goal with extends: ?P -> ?P' -> _ |- _ => assert P as p; [ clear extends | assert P' as p'; [ clear extends p | specialize (extends p p'); clear p p'] ] end.
    - split; reflexivity.
    - intro contains.
      destruct (decidableS (eqS interface (scmget_contained configuration.(cmap) listener contains).(ceinterface))) as [ e | ne ].
      * apply eqS_eq.
        symmetry.
        assumption.
      * intro e.
        apply falseS_false.
        apply ne.
        apply eq_eqS.
        symmetry.
        assumption.
    - match goal with |- match option_map (option_map _) (scmupdate _ _ ?update) with _ => _ end => destruct (scmupdate configuration.(cmap) listener update) as [ [ entry | ] | ] end; simpl in *.
      * destruct extends as [ entry' extends [ e ncontains ] ].
        split; try assumption.
        exists entry'; try assumption.
        apply e.
        intro contains.
        exfalso.
        apply ncontains.
        assumption.
      * constructor.
        destruct extends as [ contains e ].
        exists contains.
        apply eq_eqS.
        assumption.
      * destruct extends as [ contains ne ].
        exists (scmget_contained configuration.(cmap) listener contains).(ceinterface).
        ** constructor.
           exists contains.
           reflexivity.
        ** intro e.
           apply ne.
           symmetry.
           assumption.
  + destruct activated as [ [ contains e ] activated' ].
    cbn in *.
    revert activated'.
    destruct (eqS_eq e).
    rewrite convert_id.
    rewrite convertS_id.
    clear e.
    intro activated'.
    match goal with |- match option_map (option_map _) (scmupdate _ _ ?update) with _ => _ end => pose proof (scmupdate_extends configuration.(cmap) listener update) as extends end.
    simpl in extends.
    specialize (extends (fun entry => False)).
    specialize (extends (fun _ => exists2 interface', Box (GCNHKeyedS (chistory (scmget_contained configuration.(cmap) listener contains).(ceconfiguration)) listener' interface') & interface = interface' -> False)).
    specialize (extends (fun _ => Box (GCNHKeyedS (chistory (scmget_contained configuration.(cmap) listener contains).(ceconfiguration)) listener' interface))).
    specialize (extends (fun _ entry' => existsSP e: eqS entry'.(ceinterface) (scmget_contained configuration.(cmap) listener contains).(ceinterface), CExtends (scmget_contained configuration.(cmap) listener contains).(ceconfiguration) listener' activated' interface (convert e (fun interface => forall keyed, Configuration (core.(gclaction) listener interface keyed)) (fun _ => entry'.(ceconfiguration)) _))).
    match goal with extends: ?P -> ?P' -> _ |- _ => assert P as p; [ clear extends | assert P' as p'; [ clear extends p | specialize (extends p p'); clear p p'] ] end.
    - intros ncontains.
      apply falseS_false.
      apply ncontains.
      assumption.
    - intro contains'.
      merge contains contains'.
      specialize (IHlistener' _ (scmget_contained configuration.(cmap) listener contains).(ceconfiguration) activated' keyed).
      destruct (configuration_set (scmget_contained configuration.(cmap) listener contains).(ceconfiguration) listener' activated' interface keyed) as [ [ configuration' | ] | ]; simpl.
      * exists (eqS_refl _).
        rewrite convert_id.
        assumption.
      * assumption.
      * assumption.
    - match goal with |- match option_map (option_map _) (scmupdate _ _ ?update) with _ => _ end => destruct (scmupdate configuration.(cmap) listener update) as [ [ entry | ] | ] end; simpl in *.
      * destruct extends as [ entry' extends [ _ extends' ] ].
        specialize (extends' contains).
        exists entry'; assumption.
      * destruct extends as [ _ [ hkeyed ] ].
        constructor.
        exists (ex_introSS _ _ contains (eqS_refl (scmget_contained configuration.(cmap) listener contains).(ceinterface))).
        cbn.
        rewrite convert_id.
        assumption.
      * destruct extends as [ _ [ interface' [ hkeyed' ] ne ] ].
        exists interface'; try assumption.
        constructor.
        exists (ex_introSS _ _ contains (eqS_refl (scmget_contained configuration.(cmap) listener contains).(ceinterface))).
        cbn.
        rewrite convert_id.
        assumption.
Qed.

Lemma cextends_chkeyed {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} {configuration: Configuration core} {listener: GCNListener core} {activated: GCNLActivatedS (chistory configuration) listener} {interface: scheme.(Interface)} {configuration': Configuration core}: CExtends configuration listener activated interface configuration' -> GCNHKeyedS (chistory configuration') listener interface.
Proof.
  intro extends.
  induction listener as [ Transitive core listener | Transitive core listener interface' keyed' listener' ]; simpl in *.
  + destruct extends as [ _ [ entry extends [ einterface _ ] ] ].
    destruct einterface.
    cbn.
    exists (scmextends_contains_key extends).
    rewrite (scmget_contained_extends_eq extends).
    reflexivity.
  + destruct extends as [ entry extends [ e extends' ] ].
    destruct e.
    rewrite convert_id in extends'.
    destruct activated as [ [ contains einterface ] activated' ].
    apply IHlistener' in extends'; clear IHlistener'.
    destruct entry as [ interface'' keyed'' configuration'' ].
    cbn in *.
    destruct einterface.
    exists (ex_introSS _ _ (scmextends_contains_key extends) (match scmget_contained_extends_eq extends (scmextends_contains_key extends) in _ = entry return eqS (scmget_contained configuration'.(cmap) listener (scmextends_contains_key extends)).(ceinterface) entry.(ceinterface) with eq_refl => eqS_refl _ end)).
    generalize (match scmget_contained_extends_eq extends (scmextends_contains_key extends) in _ = entry return eqS (scmget_contained configuration'.(cmap) listener (scmextends_contains_key extends)).(ceinterface) entry.(ceinterface) with eq_refl => eqS_refl _ end).
    cbn.
    rewrite (scmget_contained_extends_eq extends).
    cbn.
    intro e; rewrite convert_id.
    assumption.
Qed.
Lemma chkeyed_extends {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} {configuration: Configuration core} {listener: GCNListener core} {activated: GCNLActivatedS (chistory configuration) listener} {interface: scheme.(Interface)} {configuration': Configuration core}: CExtends configuration listener activated interface configuration' -> forall {listener': GCNListener core}, forall {interface': scheme.(Interface)}, GCNHKeyedS (chistory configuration') listener' interface' -> OrS (AndS (eqS listener listener') (eqS interface interface')) (GCNHKeyedS (chistory configuration) listener' interface').
Proof.
  intros extends listener'' interface'' hkeyed''.
  induction listener as [ Transitive core listener | Transitive core listener interface' keyed' listener' IHlistener' ]; cbn in *.
  + destruct extends as [ ncontains [ entry extends [ einterface econfiguration ] ] ].
    destruct listener'' as [ listener'' | listener'' interface''' keyed''' listener''' ]; cbn in *.
    - destruct (decidableS (eqS listener listener'')) as [ e | ne ].
      * left.
        destruct e.
        split; try reflexivity.
        destruct hkeyed'' as [ contains' e ].
        destruct e.
        rewrite (scmget_contained_extends_eq extends).
        destruct einterface.
        reflexivity.
      * right.
        destruct hkeyed'' as [ contains'' e ].
        rewrite (scmget_contained_extends_neq extends ne) in e.
        eexists.
        eassumption.
    - right.
      destruct hkeyed'' as [ [ contains'' e ] hkeyed'' ].
      destruct e.
      cbn in *.
      rewrite convert_id in *.
      destruct (decidableS (eqS listener listener'')) as [ e | ne ].
      * destruct e.
        exfalso.
        apply falseS_false.
        destruct (scmget_contained_extends_eq extends contains'').
        rewrite econfiguration in hkeyed''.
        apply chkeyed_empty in hkeyed''.
        assumption.
      * pose proof contains'' as contains.
        apply (scmcontains_extends_neq extends) in contains; try assumption.
        assert (eqS (scmget_contained configuration.(cmap) listener'' contains).(ceinterface) (scmget_contained configuration'.(cmap) listener'' contains'').(ceinterface)) as einterface' by (rewrite (scmget_contained_extends_neq extends ne); reflexivity).
        exists (ex_introSS _ _ contains einterface').
        cbn.
        revert keyed''' listener''' hkeyed'' einterface'.
        rewrite (scmget_contained_extends_neq extends ne).
        intros keyed''' listener''' hkeyed'' einterface'.
        rewrite convert_id.
        assumption.
  + destruct extends as [ entry extends [ e extends' ] ].
    destruct e.
    rewrite convert_id in extends'.
    destruct activated as [ [ contains e ] activated' ].
    cbn in extends'.
    destruct listener'' as [ listener'' | listener'' interface''' keyed''' listener''' ]; cbn in *.
    - right.
      destruct hkeyed'' as [ contains'' e' ].
      destruct e'.
      destruct (decidableS (eqS listener listener'')) as [ e' | ne' ].
      * destruct e'.
        exists contains.
        destruct (scmget_contained_extends_eq extends contains'').
        assumption.
      * pose proof contains'' as contains'.
        apply (scmcontains_extends_neq extends) in contains'; try assumption.
        exists contains'.
        rewrite (scmget_contained_extends_neq extends ne').
        reflexivity.
    - destruct hkeyed'' as [ [ contains'' e''' ] hkeyed'' ].
      destruct e'''.
      cbn in hkeyed''.
      rewrite convert_id in hkeyed''.
      destruct (decidableS (eqS listener listener'')) as [ el | nel ].
      * destruct el.
        destruct (scmget_contained_extends_eq extends contains'').
        eapply IHlistener' in hkeyed''; try eassumption.
        destruct hkeyed'' as [ [ el' ei' ] | hkeyed'' ].
        ** left.
           destruct el'.
           destruct ei'.
           split; reflexivity.
        ** right.
           exists (ex_introSS _ _ contains e).
           assumption.
      * right.
        pose proof contains'' as contains'.
        apply (scmcontains_extends_neq extends) in contains'; try assumption.
        assert (eqS (scmget_contained configuration.(cmap) listener'' contains').(ceinterface) (scmget_contained configuration'.(cmap) listener'' contains'').(ceinterface)) as einterface' by (rewrite (scmget_contained_extends_neq extends nel); reflexivity).
        exists (ex_introSS _ _ contains' einterface').
        cbn.
        revert keyed''' listener''' hkeyed'' einterface'.
        rewrite (scmget_contained_extends_neq extends nel).
        intros keyed''' listener''' hkeyed'' einterface'.
        rewrite convert_id.
        assumption.
Qed.



(* Part 9.3: Subconfiguration *)

(* One configuration is a subconfiguration of another when all label-listeners resolved in the former are resolved to the same respective interfaces in the latter. *)
CoInductive SubConfiguration {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} {configuration configuration': Configuration core}: SProp :=
{ sclistener (listener: core.(GCListener)) (contains: SCMapContains configuration.(cmap) listener): SCMapContains configuration'.(cmap) listener;
  scinterface (listener: core.(GCListener)) (contains: SCMapContains configuration.(cmap) listener): eqS (scmget_contained configuration.(cmap) listener contains).(ceinterface) (scmget_contained configuration'.(cmap) listener (sclistener listener contains)).(ceinterface);
  scconfiguration (listener: core.(GCListener)) (contains: SCMapContains configuration.(cmap) listener): SubConfiguration (core := core.(gclaction) listener (scmget_contained configuration'.(cmap) listener (sclistener listener contains)).(ceinterface) _) (configuration := convert (scinterface listener contains) (fun interface => forall keyed: core.(GCLKeyedS) listener interface, Configuration (core.(gclaction) listener interface keyed)) (fun _ => (scmget_contained configuration.(cmap) listener contains).(ceconfiguration)) _) (configuration' := (scmget_contained configuration'.(cmap) listener (sclistener listener contains)).(ceconfiguration))
}.
Arguments SubConfiguration {_ _ _ _} _ _.

Lemma subconfiguration_refl {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core): SubConfiguration configuration configuration.
Proof.
  revert Transitive core core_Finite configuration; cofix subconfiguration_refl; intros Transitive core core_Finite configuration.
  refine {| sclistener listener contains := contains;
            scinterface listener contains := eqS_refl _ |}.
  intros listener contains.
  rewrite convert_id.
  apply subconfiguration_refl.
Qed.
Lemma subconfiguration_trans {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} {configuration: Configuration core} (configuration': Configuration core) {configuration'': Configuration core}: SubConfiguration configuration configuration' -> SubConfiguration configuration' configuration'' -> SubConfiguration configuration configuration''.
Proof.
  revert Transitive core core_Finite configuration configuration' configuration''; cofix subconfiguration_trans; intros Transitive core core_Finite configuration configuration' configuration'' sub sub'.
  refine {| sclistener listener contains := sub'.(sclistener) listener (sub.(sclistener) listener contains);
            scinterface listener contains := eqS_trans (sub.(scinterface) listener contains) (sub'.(scinterface) listener (sub.(sclistener) listener contains)) |}.
  intros listener contains.
  rewrite <- convert_convert.
  eapply subconfiguration_trans; try apply sub'.(scconfiguration).
  generalize (sub'.(scinterface) listener (sub.(sclistener) listener contains)).
  destruct (scmget_contained configuration''.(cmap) listener (sub'.(sclistener) listener (sub.(sclistener) listener contains))) as [ interface keyed configuration''' ].
  cbn.
  intro e.
  destruct e; rewrite convert_id.
  apply sub.(scconfiguration).
Qed.

Lemma subconfiguration_subhistory {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} {configuration configuration': Configuration core}: SubConfiguration configuration configuration' -> SubHistory (chistory configuration) (chistory configuration').
Proof.
  intros sub listener interface hkeyed.
  induction listener as [ Transitive core listener | Transitive core listener interface' keyed' listener' IHlistener' ]; cbn in *.
  + destruct hkeyed as [ contains e ].
    exists (sub.(sclistener) listener contains).
    destruct (sub.(scinterface) listener contains).
    assumption.
  + destruct hkeyed as [ [ contains e ] hkeyed ].
    destruct e.
    cbn in *.
    rewrite convert_id in *.
    exists (ex_introSS _ _ (sub.(sclistener) listener contains) (eqS_sym (sub.(scinterface) listener contains))).
    cbn.
    eapply IHlistener'; try eassumption.
    generalize (sub.(scconfiguration) listener contains).
    cbn.
    generalize (scmget_contained configuration'.(cmap) listener (sub.(sclistener) listener contains)).(ceconfiguration).
    generalize (scmget_contained configuration'.(cmap) listener (sub.(sclistener) listener contains)).(cekeyed).
    destruct (sub.(scinterface) listener contains).
    rewrite convert_id.
    rewrite convert_id.
    trivial.
Qed.

Lemma cextends_sub {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} {configuration: Configuration core} {listener: GCNListener core} {activated: GCNLActivatedS (chistory configuration) listener} {interface: scheme.(Interface)} {configuration': Configuration core}: CExtends configuration listener activated interface configuration' -> SubConfiguration configuration configuration'.
Proof.
  intro extends.
  induction listener as [ Transitive core listener | Transitive core listener interface' keyed' listener' IHlistener' ]; simpl in extends.
  + destruct extends as [ ncontains [ entry extends _ ] ].
    clear activated.
    pose proof (fun (listener': core.(GCListener)) contains' => scmextends_contains extends (k' := listener') contains') as slistener.
    assert (forall listener contains, eqS (scmget_contained configuration.(cmap) listener contains).(ceinterface) (scmget_contained configuration'.(cmap) listener (slistener listener contains)).(ceinterface)) as sinterface.
    - intros listener' contains'.
      destruct (decidableS (eqS listener listener')) as [ e | ne ].
      * destruct e.
        exfalso.
        auto.
      * rewrite (scmget_contained_extends_neq extends ne).
        merge (scmcontains_extends_neq extends (slistener listener' contains') ne) contains'.
        reflexivity.
    - exists slistener sinterface.
      intros listener' contains'.
      destruct (decidableS (eqS listener listener')) as [ e | ne ].
      * destruct e.
        exfalso.
        auto.
      * generalize (sinterface listener' contains').
        clear sinterface.
        rewrite (scmget_contained_extends_neq extends ne).
        merge (scmcontains_extends_neq extends (slistener listener' contains') ne) contains'.
        intro e.
        rewrite convert_id.
        apply subconfiguration_refl.
  + destruct extends as [ entry extends [ e extends'] ].
    destruct e.
    rewrite convert_id in extends'.
    simpl in activated.
    destruct activated as [ [ contains e ] activated' ].
    cbn in extends'.
    apply IHlistener' in extends'; clear IHlistener'.
    pose proof (fun (listener': core.(GCListener)) contains' => scmextends_contains extends (k' := listener') contains') as slistener.
    assert (forall listener contains, eqS (scmget_contained configuration.(cmap) listener contains).(ceinterface) (scmget_contained configuration'.(cmap) listener (slistener listener contains)).(ceinterface)) as sinterface.
    - intros listener'' contains''.
      destruct (decidableS (eqS listener listener'')) as [ e' | ne ].
      * destruct e'.
        rewrite (scmget_contained_extends_eq extends).
        merge contains contains''.
        assumption.
      * rewrite (scmget_contained_extends_neq extends ne).
        merge (scmcontains_extends_neq extends (slistener listener'' contains'') ne) contains''.
        reflexivity.
    - exists slistener sinterface.
      intros listener'' contains''.
      generalize (sinterface listener'' contains''); clear sinterface.
      destruct (decidableS (eqS listener listener'')) as [ e' | ne ].
      * destruct e'.
        rewrite (scmget_contained_extends_eq extends).
        intro e'.
        merge e e'.
        assumption.
      * rewrite (scmget_contained_extends_neq extends ne).
        merge (scmcontains_extends_neq extends (slistener listener'' contains'') ne) contains''.
        intro e'.
        rewrite convert_id.
        apply subconfiguration_refl.
Qed.



(* Part 9.4: Constraint-Activation
 * When a (nested) label-listener becomes resolved, a number of new constraints become activated.
 * gcnl_constraints collects that list of constraints and constraint_extends proves it has the expected properties.
 *)

Definition gcnl_constraints {Interface_SSet: SSet scheme.(Interface)}: forall {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (listener: GCNListener core) (interface: scheme.(Interface)) (keyed: GCNLKeyedS listener interface), list (GCNConstraint core)
:= fix gcnl_constraints {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (listener: GCNListener core) {struct listener}: forall interface: scheme.(Interface), GCNLKeyedS listener interface -> list (GCNConstraint core)
:= match listener as listener return forall interface: scheme.(Interface), GCNLKeyedS listener interface -> list (GCNConstraint core) with
   | gcnllistener listener => fun interface keyed => flist (fun constraint: (core.(gclaction) listener interface keyed).(GCConstraint) => gcncnested listener interface keyed (gcncconstraint constraint))
   | gcnlnested listener interface keyed listener' => fun interface' keyed' => map (gcncnested listener interface keyed) (gcnl_constraints listener' interface' keyed')
   end.
Lemma constraint_extends {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} {configuration: Configuration core} {listener: GCNListener core} {activated: GCNLActivatedS (chistory configuration) listener} {interface: scheme.(Interface)} {configuration': Configuration core}: forall extends: CExtends configuration listener activated interface configuration', AndS (ListForallS (GCNCActivatedS (chistory configuration')) (gcnl_constraints listener interface (gcnhkeyed (cextends_chkeyed extends)))) (forall constraint: GCNConstraint core, GCNCActivatedS (chistory configuration') constraint -> OrS (GCNCActivatedS (chistory configuration) constraint) (ListContains constraint (gcnl_constraints listener interface (gcnhkeyed (cextends_chkeyed extends))))).
Proof.
  intro extends.
  generalize (gcnhkeyed (cextends_chkeyed extends)).
  intro keyed.
  induction listener as [ Transitive core listener | Transitive core listener interface' keyed' listener' IHlistener' ]; cbn in *.
  + clear activated.
    destruct extends as [ ncontains [ entry extends [ einterface econfiguration ] ] ].
    destruct entry as [ interface' keyed' configuration'' ].
    cbn in *.
    subst.
    merge keyed keyed'.
    split.
    - apply flist_forall.
      cbn.
      intro constraint.
      repeat split.
      exists (scmextends_contains_key extends).
      rewrite (scmget_contained_extends_eq extends).
      reflexivity.
    - intros constraint activated.
      destruct constraint as [ constraint | listener' interface' keyed' constraint ]; cbn in *.
      * left.
        split.
      * destruct activated as [ [ contains' e ] activated ].
        destruct e.
        cbn in *.
        rewrite convert_id in activated.
        revert keyed' constraint activated.
        destruct (decidableS (eqS listener listener')) as [ e | ne ].
        ** destruct e.
           rewrite (scmget_contained_extends_eq extends).
           cbn.
           intros keyed' constraint activated.
           destruct constraint as [ constraint | listener'' interface'' keyed'' constraint]; cbn in *.
           *** right.
               apply (contains_flist (fun constraint => gcncnested listener interface keyed (gcncconstraint constraint))).
           *** destruct activated as [ [ [ ] _] _ ].
        ** rewrite (scmget_contained_extends_neq extends ne).
           intros keyed' constraint activated.
           left.
           exists (ex_introSS _ _ _ (eqS_refl (scmget_contained configuration.(cmap) listener' _).(ceinterface))).
           cbn.
           rewrite convert_id.
           assumption.
  + destruct activated as [ [ contains e ] activated' ].
    destruct e.
    cbn in *.
    destruct extends as [ entry' extends [ e extends' ] ].
    revert activated' extends'.
    rewrite convert_id.
    intros activated' extends'.
    destruct entry' as [ interface' keyed'' configuration'' ].
    cbn in *.
    destruct (eqS_sym e); rewrite convert_id in extends'; clear e.
    apply IHlistener' with (keyed := keyed) in extends'; clear IHlistener'.
    destruct extends' as [ constraints_activated activated_constraints ].
    split.
    - apply forall_map.
      simpl.
      revert constraints_activated.
      apply listforallS_mono.
      intros constraint activated''.
      cbn.
      exists (ex_introSS _ _ (scmextends_contains_key extends) (match scmget_contained_extends_eq extends (scmextends_contains_key extends) in _ = entry return eqS (scmget_contained configuration'.(cmap) listener (scmextends_contains_key extends)).(ceinterface) entry.(ceinterface) with eq_refl => eqS_refl _ end)).
      cbn.
      generalize (scmget_contained_extends_eq extends (scmextends_contains_key extends)).
      generalize (scmget_contained configuration'.(cmap) listener (scmextends_contains_key extends)).
      intros entry e.
      destruct (eq_sym e).
      cbn.
      rewrite convert_id.
      assumption.
    - intros constraint activated.
      destruct constraint as [ constraint | listener''' interface''' keyed''' constraint ]; cbn in *.
      * left.
        split.
      * destruct activated as [ [ contains''' e ] activated ].
        destruct e.
        cbn in activated.
        rewrite convert_id in activated.
        revert keyed''' constraint activated.
        destruct (decidableS (eqS listener listener''')) as [ e | ne ].
        ** destruct e.
           rewrite (scmget_contained_extends_eq extends).
           cbn.
           intros keyed''' constraint activated.
           merge keyed' keyed'''.
           apply activated_constraints in activated.
           destruct activated as [ activated | contains' ].
           *** left.
               exists (ex_introSS _ _ contains (eqS_refl (scmget_contained configuration.(cmap) listener contains).(ceinterface))).
               cbn.
               rewrite convert_id.
               assumption.
           *** right.
               apply contains_map.
               assumption.
        ** rewrite (scmget_contained_extends_neq extends ne).
           intros keyed''' constraint activated.
           left.
           exists (ex_introSS _ _ _ (eqS_refl (scmget_contained configuration.(cmap) listener''' _).(ceinterface))).
           cbn.
           rewrite convert_id.
           assumption.
Qed.



(* Part 9.5: Indexing
 * Here we assign paths to the nested components of a graphical core, which will be used to index them for indexed maps and sets.
 * This path assignment ignores the interface used as activation requirements for nested components, and as such distinct nested components can be assigned the path.
 * However, because the algorithm only resolves a label-listener to at most one interface at any point in time, we know path assignments are unique for at least the currently activated components.
 * In this way, we can carry over the indexed data structures used each time an event fires, rather than have to reindex them, even if the graphical core has an infinite number of permitted resolutions for a given label-listener.
 * Furthermore, given a current configuration, we know that its key-set is finite and consequently provides a finite bound on the set of activated components, which we can use to ensure constraint-derivation within a configuration terminates.
 *)

Definition gcnnpath: forall {Transitive: Sort} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core}, GCNNode core -> BPath
:= fix gcnnpath {Transitive: Sort} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (node: GCNNode core) {struct node}: BPath
:= match node with
   | gcnnnode node => bfirst (scpath node)
   | gcnnnested listener interface keyed node => bsecond (scmpath listener (gcnnpath node))
   end.
Definition gcnntrunk {IParameter_SubFinite: forall interface: scheme.(Interface), SubFinite (scheme.(IParameter) interface)}: forall {Transitive: Sort} `{SubFiniteSort Transitive} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (configuration: Configuration core), BTrunk
:= fix gcnntrunk {Transitive: Sort} `{SubFiniteSort Transitive} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (configuration: Configuration core): BTrunk
:= bbranch oabsent
           (sftrunk core.(GCNode))
           (scmtrunk configuration.(cmap) (fun listener entry => gcnntrunk entry.(ceconfiguration))).
Lemma gcnnpath_inj {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubCountable: forall interface: scheme.(Interface), SubCountable (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubCountable: SubCountableSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (node node': GCNNode core): GCNNActivatedS (chistory configuration) node -> GCNNActivatedS (chistory configuration) node' -> gcnnpath node = gcnnpath node' -> node = node'.
Proof.
  intros activated activated' e.
  induction node; destruct node'; simpl in *; try inversion_hset e.
  + rename H0 into e.
    apply scpath_inj in e.
    destruct e.
    reflexivity.
  + rename H0 into e.
    apply scmpath_inj in e.
    destruct e as [ e enode ].
    destruct e.
    destruct activated as [ hkeyed activated ].
    destruct activated' as [ hkeyed' activated' ].
    pose proof hkeyed' as e.
    apply ((chistory_final configuration).(fgchunique) hkeyed) in e.
    apply eqS_eq in e.
    destruct e.
    merge hkeyed hkeyed'.
    destruct hkeyed as [ contains e ].
    cbn in *.
    destruct (eqS_eq e).
    rewrite convert_id in activated.
    rewrite convert_id in activated'.
    specialize (IHnode (pair _ (pair _ _)) _ (scmget_contained configuration.(cmap) listener contains).(ceconfiguration)).
    apply IHnode in enode; try assumption.
    destruct enode.
    reflexivity.
Qed.
Lemma gcnntrunk_contains {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubFinite: forall interface: scheme.(Interface), SubFinite (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubFinite: SubFiniteSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (node: GCNNode core): GCNNActivatedS (chistory configuration) node -> BTContains (gcnntrunk configuration) (gcnnpath node).
Proof.
  intro activated.
  induction node; destruct core_Finite as [ gca_SubFinite gcn_SubFinite gcl_SubFinite gcc_Finite gclk_Decidable gcla_Finite ]; simpl in activated; simpl.
  + apply sfcontains.
  + destruct activated as [ [ contains e ] activated ].
    cbn in activated.
    destruct (eqS_eq e); merge_refl e; rewrite convert_id in activated.
    specialize (IHnode _ _ _ activated).
    apply scmtrunk_contains with contains.
    eassumption.
Qed.

Definition gcnlpath: forall {Transitive: Sort} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core}, GCNListener core -> BPath
:= fix gcnlpath {Transitive: Sort} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (listener: GCNListener core) {struct listener}: BPath
:= match listener with
   | gcnllistener listener => bfirst (scpath listener)
   | gcnlnested listener interface keyed listener' => bsecond (bpath_pair (scpath listener) (gcnlpath listener'))
   end.
Definition gcnltrunk {IParameter_SubFinite: forall interface: scheme.(Interface), SubFinite (scheme.(IParameter) interface)}: forall {Transitive: Sort} `{SubFiniteSort Transitive} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (configuration: Configuration core), BTrunk
:= fix gcnltrunk {Transitive: Sort} `{SubFiniteSort Transitive} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (configuration: Configuration core): BTrunk
:= bbranch oabsent 
           (sftrunk core.(GCListener))
           (scmtrunk configuration.(cmap) (fun listener entry => gcnltrunk entry.(ceconfiguration))).
Lemma gcnlpath_inj {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubCountable: forall interface: scheme.(Interface), SubCountable (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubCountable: SubCountableSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (listener listener': GCNListener core): GCNLActivatedS (chistory configuration) listener -> GCNLActivatedS (chistory configuration) listener' -> gcnlpath listener = gcnlpath listener' -> listener = listener'.
Proof.
  intros activated activated' e.
  induction listener; destruct listener'; simpl in *; try inversion_hset e.
  + rename H0 into e.
    apply scpath_inj in e.
    destruct e.
    reflexivity.
  + rename H0 into e.
    apply scmpath_inj in e.
    destruct e as [ e elistener ].
    destruct e.
    destruct activated as [ hkeyed activated ].
    destruct activated' as [ hkeyed' activated' ].
    pose proof hkeyed' as e.
    apply ((chistory_final configuration).(fgchunique) hkeyed) in e.
    apply eqS_eq in e.
    destruct e.
    merge hkeyed hkeyed'.
    destruct hkeyed as [ contains e ].
    cbn in *.
    destruct (eqS_eq e).
    rewrite convert_id in activated.
    rewrite convert_id in activated'.
    specialize (IHlistener (pair _ (pair _ _)) _ (scmget_contained configuration.(cmap) listener contains).(ceconfiguration)).
    apply IHlistener in elistener; try assumption.
    destruct elistener.
    reflexivity.
Qed.
Lemma gcnltrunk_contains {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubFinite: forall interface: scheme.(Interface), SubFinite (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubFinite: SubFiniteSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (listener: GCNListener core): GCNLActivatedS (chistory configuration) listener -> BTContains (gcnltrunk configuration) (gcnlpath listener).
Proof.
  intro activated.
  induction listener; destruct core_Finite as [ gca_SubFinite gcn_SubFinite gcl_SubFinite gcc_Finite gclk_Decidable gcla_Finite ]; simpl in activated; simpl.
  + apply sfcontains.
  + destruct activated as [ [ contains e ] activated ].
    cbn in activated.
    destruct (eqS_eq e); merge_refl e; rewrite convert_id in activated.
    specialize (IHlistener _ _ _ activated).
    apply scmtrunk_contains with contains.
    eassumption.
Qed.

Definition gccpath {Transitive: Sort} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (concrete: GCConcrete core): BPath
:= match concrete with
   | gcclistener listener => bfirst (gcnlpath listener)
   | gccnode node => bsecond (gcnnpath node)
   | gccany => bend
   end.
Definition gcctrunk {IParameter_SubFinite: forall interface: scheme.(Interface), SubFinite (scheme.(IParameter) interface)} {Transitive: Sort} `{SubFiniteSort Transitive} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (configuration: Configuration core): BTrunk
:= bbranch opresent
           (gcnltrunk configuration)
           (gcnntrunk configuration).
Lemma gccpath_inj {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubCountable: forall interface: scheme.(Interface), SubCountable (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubCountable: SubCountableSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (concrete concrete': GCConcrete core): GCCActivatedS (chistory configuration) concrete -> GCCActivatedS (chistory configuration) concrete' -> gccpath concrete = gccpath concrete' -> concrete = concrete'.
Proof.
  intros activated activated' e.
  destruct concrete; destruct concrete'; simpl in *; try inversion_hset e.
  + rename H0 into e.
    eapply gcnlpath_inj in e; try eassumption.
    destruct e.
    reflexivity.
  + rename H0 into e.
    eapply gcnnpath_inj in e; try eassumption.
    destruct e.
    reflexivity.
  + reflexivity.
Qed.
Lemma gcctrunk_contains {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubFinite: forall interface: scheme.(Interface), SubFinite (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubFinite: SubFiniteSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (concrete: GCConcrete core): GCCActivatedS (chistory configuration) concrete -> BTContains (gcctrunk configuration) (gccpath concrete).
Proof.
  intro activated.
  destruct concrete; simpl in *.
  * apply gcnltrunk_contains.
    assumption.
  * apply gcnntrunk_contains.
    assumption.
  * constructor.
Qed.

Definition gcntpath {IParameter_SubCountable: forall interface: scheme.(Interface), SubCountable (scheme.(IParameter) interface)}: forall {Transitive: Sort} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core}, GCNTransitive core -> BPath
:= fix gcntpath {Transitive: Sort} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (transitive: GCNTransitive core) {struct transitive}: BPath
:= match transitive with
   | gcntabstract abstract => bfirst (scpath abstract)
   | gcntargument listener interface keyed parameter => bsecond (bfirst (scmpath listener (scpath parameter)))
   | gcntnested listener interface keyed transitive => bsecond (bsecond (scmpath listener (gcntpath transitive)))
   end.
Definition gcnttrunk {IParameter_SubFinite: forall interface: scheme.(Interface), SubFinite (scheme.(IParameter) interface)}: forall {Transitive: Sort} `{SubFiniteSort Transitive} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (configuration: Configuration core), BTrunk
:= fix gcnttrunk {Transitive: Sort} `{SubFiniteSort Transitive} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (configuration: Configuration core): BTrunk
:= bbranch oabsent 
           (sftrunk core.(GCAbstract))
           (bbranch oabsent
                    (scmtrunk configuration.(cmap) (fun listener entry => sftrunk (scheme.(IParameter) entry.(ceinterface))))
                    (scmtrunk configuration.(cmap) (fun listener entry => gcnttrunk entry.(ceconfiguration)))).
Lemma gcntpath_inj {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubCountable: forall interface: scheme.(Interface), SubCountable (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubCountable: SubCountableSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (transitive transitive': GCNTransitive core): GCNTActivatedS (chistory configuration) transitive -> GCNTActivatedS (chistory configuration) transitive' -> gcntpath transitive = gcntpath transitive' -> transitive = transitive'.
Proof.
  intros activated activated' e.
  induction transitive; destruct transitive'; simpl in *; try inversion_hset e.
  + rename H0 into e.
    apply scpath_inj in e.
    destruct e.
    reflexivity.
  + rename H0 into e.
    apply scmpath_inj in e.
    destruct e as [ elistener eparameter ].
    destruct elistener.
    apply ((chistory_final configuration).(fgchunique) activated) in activated'.
    apply eqS_eq in activated'.
    destruct activated'.
    apply scpath_inj in eparameter.
    destruct eparameter.
    reflexivity.
  + rename H0 into e.
    apply scmpath_inj in e.
    destruct e as [ elistener etransitive ].
    destruct elistener.
    destruct activated as [ hkeyed activated ].
    destruct activated' as [ hkeyed' activated' ].
    pose proof hkeyed' as e.
    apply ((chistory_final configuration).(fgchunique) hkeyed) in e.
    apply eqS_eq in e.
    destruct e.
    merge hkeyed hkeyed'.
    destruct hkeyed as [ contains e ].
    cbn in *.
    destruct (eqS_eq e).
    rewrite convert_id in activated.
    rewrite convert_id in activated'.
    specialize (IHtransitive (pair _ (pair _ _)) _ (scmget_contained configuration.(cmap) listener contains).(ceconfiguration)).
    apply IHtransitive in etransitive; try assumption.
    destruct etransitive.
    reflexivity.
Qed.
Lemma gcnttrunk_contains {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubFinite: forall interface: scheme.(Interface), SubFinite (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubFinite: SubFiniteSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (transitive: GCNTransitive core): GCNTActivatedS (chistory configuration) transitive -> BTContains (gcnttrunk configuration) (gcntpath transitive).
Proof.
  intro activated.
  induction transitive; destruct core_Finite as [ gca_SubFinite gcn_SubFinite gcl_SubFinite gcc_Finite gclk_Decidable gcla_Finite ]; simpl in activated; simpl.
  + apply sfcontains.
  + destruct activated as [ contains e ].
    destruct (eqS_eq e); merge_refl e.
    apply scmtrunk_contains with contains.
    apply sfcontains.
  + destruct activated as [ [ contains e ] activated ].
    cbn in activated.
    destruct (eqS_eq e); merge_refl e; rewrite convert_id in activated.
    specialize (IHtransitive _ _ _ activated).
    apply scmtrunk_contains with contains.
    eassumption.
Qed.

Definition gctpath {IParameter_SubCountable: forall interface: scheme.(Interface), SubCountable (scheme.(IParameter) interface)} {Transitive: Sort} `{SubCountableSort Transitive} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (transitive: GCTransitive core): BPath
:= match transitive with
   | gctntransitive transitive => bfirst (gcntpath transitive)
   | gcttransitive transitive => bsecond (scpath transitive)
   end.
Definition gcttrunk {IParameter_SubFinite: forall interface: scheme.(Interface), SubFinite (scheme.(IParameter) interface)} {Transitive: Sort} `{SubFiniteSort Transitive} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (configuration: Configuration core): BTrunk
:= bbranch oabsent
           (gcnttrunk configuration)
           (sftrunk (SumSort Transitive)).
Lemma gctpath_inj {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubCountable: forall interface: scheme.(Interface), SubCountable (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubCountable: SubCountableSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (transitive transitive': GCTransitive core): GCTActivatedS (chistory configuration) transitive -> GCTActivatedS (chistory configuration) transitive' -> gctpath transitive = gctpath transitive' -> transitive = transitive'.
Proof.
  intros activated activated' e.
  destruct transitive; destruct transitive'; simpl in *; try inversion_hset e.
  + rename H0 into e.
    eapply gcntpath_inj in e; try eassumption.
    destruct e.
    reflexivity.
  + rename H0 into e.
    apply scpath_inj in e.
    destruct e.
    reflexivity.
Qed.
Lemma gcttrunk_contains {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubFinite: forall interface: scheme.(Interface), SubFinite (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubFinite: SubFiniteSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (transitive: GCTransitive core): GCTActivatedS (chistory configuration) transitive -> BTContains (gcttrunk configuration) (gctpath transitive).
Proof.
  intro activated.
  destruct transitive; simpl in *.
  * apply gcnttrunk_contains.
    assumption.
  * rewrite <- SumSort_SubFinite_SubCountable.
    apply sfcontains.
Qed.

Definition gcapath {IParameter_SubCountable: forall interface: scheme.(Interface), SubCountable (scheme.(IParameter) interface)} {Transitive: Sort} `{SubCountableSort Transitive} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (atom: GCAtom core): BPath
:= match atom with
   | gcaconcrete concrete => bfirst (gccpath concrete)
   | gcatransitive transitive => bsecond (gctpath transitive)
   end.
Definition gcatrunk {IParameter_SubFinite: forall interface: scheme.(Interface), SubFinite (scheme.(IParameter) interface)} {Transitive: Sort} `{SubFiniteSort Transitive} {core: GraphicalCore Transitive} `{FiniteGraphicalCore Transitive core} (configuration: Configuration core): BTrunk
:= bbranch oabsent
           (gcctrunk configuration)
           (gcttrunk configuration).
Lemma gcapath_inj {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubCountable: forall interface: scheme.(Interface), SubCountable (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubCountable: SubCountableSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (atom atom': GCAtom core): GCAActivatedS (chistory configuration) atom -> GCAActivatedS (chistory configuration) atom' -> gcapath atom = gcapath atom' -> atom = atom'.
Proof.
  intros activated activated' e.
  destruct atom; destruct atom'; simpl in *; try inversion_hset e.
  + rename H0 into e.
    eapply gccpath_inj in e; try eassumption.
    destruct e.
    reflexivity.
  + rename H0 into e.
    eapply gctpath_inj in e; try eassumption.
    destruct e.
    reflexivity.
Qed.
Lemma gcatrunk_contains {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubFinite: forall interface: scheme.(Interface), SubFinite (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubFinite: SubFiniteSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (atom: GCAtom core): GCAActivatedS (chistory configuration) atom -> BTContains (gcatrunk configuration) (gcapath atom).
Proof.
  intro activated.
  destruct atom; simpl in *.
  * apply gcctrunk_contains.
    assumption.
  * apply gcttrunk_contains.
    assumption.
Qed.

Lemma gcapath_injS {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubCountable: forall interface: scheme.(Interface), SubCountable (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubCountable: SubCountableSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} (configuration: Configuration core) (atom atom': GCAtom core): GCAActivatedS (chistory configuration) atom -> GCAActivatedS (chistory configuration) atom' -> eqS (gcapath atom) (gcapath atom') -> eqS atom atom'.
Proof.
  intros activated activated' e.
  apply eqS_eq in e.
  eapply gcapath_inj in e; try eassumption.
  apply eq_eqS.
  assumption.
Qed.
Lemma gcaeq_deciderS {Interface_SSet: SSet scheme.(Interface)} {IParameter_SubCountable: forall interface: scheme.(Interface), SubCountable (scheme.(IParameter) interface)} {Transitive: Sort} {Transitive_SubCountable: SubCountableSort Transitive} {core: GraphicalCore Transitive} {core_Finite: FiniteGraphicalCore core} {configuration: Configuration core} (atom atom': GCAtom core): GCAActivatedS (chistory configuration) atom -> GCAActivatedS (chistory configuration) atom' -> DeciderS (eqS atom atom').
Proof.
  intros activated activated'.
  destruct (decidableS (eqS (gcapath atom) (gcapath atom'))) as [ e | ne ].
  + left.
    eapply gcapath_injS in e; eassumption.
  + right.
    intro e.
    apply ne.
    destruct e.
    reflexivity.
Qed.



(* Part 10: Algorithm
 * Here we prove that graphical-core consistency is decidable.
 * Unfortunately the loop invariant required to ensure termination is quite large, so the algorithm is itself buried in the proof.
 * Nonetheless, it proceeds as described in the paper.
 *)

(* Part 10.1: Partial Constraint-Derivation
 * A major challenge of the proof is describing the invariant of the intermediate state of the algorithm.
 * A key part of describing the algorithm's intermediate behavior is describing the constraints that the algorithm still needs to (eventually) derive given its current state.
 * DerivedWithin indicates that a constraint can be derived from the constraints in the worklist (W) without passing through a constraint that has already been processed (P) assuming that all processed lower/upper bounds on transitives are given by (L/U).
 * W will be the pairs occuring in the worklist; P will be the pairs in the processed set; and L/U will be the key-value pairs in the lower/upper-bound tracking sets.
 *)
Unset Elimination Schemes.
Inductive DerivedWithin `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {P W: GCAtom core -> GCAtom core -> SProp} {L U: GCTransitive core -> GCAtom core -> SProp}: GCAtom core -> GCAtom core -> SProp
:= dwstep (atom atom': GCAtom core): GCAActivatedS history atom -> GCAActivatedS history atom' -> (P atom atom' -> FalseS) -> DerivedWithinStep atom atom' -> DerivedWithin atom atom'
with DerivedWithinStep `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {P W: GCAtom core -> GCAtom core -> SProp} {L U: GCTransitive core -> GCAtom core -> SProp}: GCAtom core -> GCAtom core -> SProp
:= dwcontravariant (atom atom': GCAtom core): SDerivedWithinStep negative atom atom' -> DerivedWithinStep atom' atom
 | dwcovariant (atom atom': GCAtom core): SDerivedWithinStep positive atom atom' -> DerivedWithinStep atom atom'
 | dwwork (atom atom': GCAtom core): W atom atom' -> DerivedWithinStep atom atom'
 | dwconstraint (constraint: GCNConstraint core): GCNCActivatedS history constraint -> DerivedWithinStep (apply_elimination (gcatomize core) (gcnclower constraint)) (apply_elimination (gcatomizel core) (gcncupper constraint))
 | dwtransitive (atom: GCAtom core) (transitive': GCTransitive core) (atom'': GCAtom core): DerivedWithin atom (gcatransitive transitive') -> DerivedWithin (gcatransitive transitive') atom'' -> DerivedWithinStep atom atom''
 | dwlower (atom: GCAtom core) (transitive': GCTransitive core) (atom'': GCAtom core): L transitive' atom -> DerivedWithin (gcatransitive transitive') atom'' -> DerivedWithinStep atom atom''
 | dwupper (atom: GCAtom core) (transitive': GCTransitive core) (atom'': GCAtom core): DerivedWithin atom (gcatransitive transitive') -> U transitive' atom'' -> DerivedWithinStep atom atom''
with SDerivedWithinStep `{SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {P W: GCAtom core -> GCAtom core -> SProp} {L U: GCTransitive core -> GCAtom core -> SProp}: Sign -> GCAtom core -> GCAtom core -> SProp
:= dwnode (node node': GCNNode core) (e: eqS (gcnninterface node) (gcnninterface node')) (parameter: scheme.(IParameter) (gcnninterface node)): DerivedWithin (gcaconcrete (gccnode node)) (gcaconcrete (gccnode node')) -> SDerivedWithinStep ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument node parameter)) (apply_elimination (gcatomize core) (gcnnargument node' (convert e scheme.(IParameter) parameter)))
 | dwlistener (node: GCNNode core) (listener': GCNListener core) (interface': scheme.(Interface)) (hkeyed': GCNHKeyedS history listener' interface') (e: eqS (gcnninterface node) interface') (parameter: scheme.(IParameter) (gcnninterface node)): DerivedWithin (gcaconcrete (gccnode node)) (gcaconcrete (gcclistener listener')) -> SDerivedWithinStep ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument node parameter)) (gcatransitive (gctntransitive (gcntlargument listener' interface' (gcnhkeyed hkeyed') (convert e scheme.(IParameter) parameter)))).
Arguments DerivedWithin {_ _ _} _ _ _ _ _ _ _.
Arguments DerivedWithinStep {_ _ _} _ _ _ _ _ _ _.
Arguments SDerivedWithinStep {_ _ _} _ _ _ _ _ _ _ _.
Scheme DerivedWithin_sind := Minimality for DerivedWithin Sort SProp
  with DerivedWithinStep_sind := Minimality for DerivedWithinStep Sort SProp
  with SDerivedWithinStep_sind := Minimality for SDerivedWithinStep Sort SProp.
Arguments DerivedWithin_sind {_ _ _ _ _ _ _ _}.
Set Elimination Schemes.

Lemma sderivedwithinstep_signed {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {P W: GCAtom core -> GCAtom core -> SProp} {L U: GCTransitive core -> GCAtom core -> SProp} (sign: Sign) (atom atom': GCAtom core): SDerivedWithinStep history P W L U sign atom atom' -> Signed (DerivedWithinStep history P W L U) sign atom atom'.
Proof.
  intro derived.
  destruct sign.
  + apply dwcontravariant.
    assumption.
  + apply dwcovariant.
    assumption.
Qed.
Lemma sderivedwithin_signed {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {P W: GCAtom core -> GCAtom core -> SProp} {L U: GCTransitive core -> GCAtom core -> SProp} (sign: Sign) (atom atom': GCAtom core): GCAActivatedS history atom -> GCAActivatedS history atom' -> (Signed P sign atom atom' -> FalseS) -> SDerivedWithinStep history P W L U sign atom atom' -> Signed (DerivedWithin history P W L U) sign atom atom'.
Proof.
  intros activated activated' np derived.
  apply sderivedwithinstep_signed in derived; try assumption.
  destruct sign; apply dwstep; assumption.
Qed.

Lemma derivedwithin_mono {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {P P' W W': GCAtom core -> GCAtom core -> SProp} {L L' U U': GCTransitive core -> GCAtom core -> SProp}: (forall atom atom': GCAtom core, P' atom atom' -> P atom atom') -> (forall atom atom': GCAtom core, W atom atom' -> W' atom atom') -> (forall transitive: GCTransitive core, forall lower: GCAtom core, L transitive lower -> L' transitive lower) -> (forall transitive: GCTransitive core, forall upper: GCAtom core, U transitive upper -> U' transitive upper) -> forall atom atom': GCAtom core, DerivedWithin history P W L U atom atom' -> DerivedWithin history P' W' L' U' atom atom'.
Proof.
  intros p'p ww' ll' uu'.
  apply (DerivedWithin_sind (DerivedWithin history P' W' L' U') (DerivedWithinStep history P' W' L' U') (SDerivedWithinStep history P' W' L' U')); intros.
  + apply dwstep; auto.
  + apply dwcontravariant; auto.
  + apply dwcovariant; auto.
  + apply dwwork; auto.
  + apply dwconstraint; auto.
  + eapply dwtransitive; eauto.
  + eapply dwlower; eauto.
  + eapply dwupper; eauto.
  + apply dwnode; auto.
  + apply dwlistener; auto.
Qed.

(* If all activated constraints are processed, and the worklist is empty, then DerivedWithin (for any L/U) is empty. *)
Lemma derivedwithin_processed_false {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {P W: GCAtom core -> GCAtom core -> SProp} {L U: GCTransitive core -> GCAtom core -> SProp} {atom atom': GCAtom core}: (forall constraint: GCNConstraint core, GCNCActivatedS history constraint -> P (apply_elimination (gcatomize core) (gcnclower constraint)) (apply_elimination (gcatomizel core) (gcncupper constraint))) -> (forall atom atom': GCAtom core, W atom atom' -> FalseS) -> DerivedWithin history P W L U atom atom' -> FalseS.
Proof.
  intros pconstraint cfalse.
  apply (DerivedWithin_sind (fun _ _ => FalseS) (fun atom atom' => (P atom atom' -> FalseS) -> FalseS) (fun _ _ _ => FalseS)); try eauto.
Qed.

(* If there are no processed constraints, then DerivedWithin (for any W/L/U) contains all derived constraints. *)
Lemma derived_within {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {P W: GCAtom core -> GCAtom core -> SProp} {L U: GCTransitive core -> GCAtom core -> SProp}: (forall atom atom': GCAtom core, P atom atom' -> FalseS) -> forall {sign: Sign} {atom atom': GCAtom core}, SDerived history sign atom atom' -> Signed (DerivedWithin history P W L U) sign atom atom'.
Proof.
  intros nprocessed sign atom atom' derived.
  induction derived; simpl in *.
  + assumption.
  + apply dwstep.
    - apply constraint_activated.
      assumption.
    - apply constraint_activated.
      assumption.
    - apply nprocessed.
    - apply dwconstraint.
      assumption.
  + apply dwstep.
    - apply (sderived_activated derived1).
    - apply (sderived_activated derived2).
    - apply nprocessed.
    - apply dwtransitive with transitive'; assumption.
  + apply sderivedwithin_signed; try (apply gcnnargument_activated; apply (sderived_activated derived)).
    - destruct ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter); apply nprocessed.
    - apply dwnode.
      assumption.
  + apply sderivedwithin_signed; try (apply gcnnargument_activated || apply gcntlargument_activated; apply (sderived_activated derived)).
    - destruct ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter); apply nprocessed.
    - apply dwlistener.
      assumption.
Qed.



Definition SignedPairEqS {T: Type} (t1 t2: T): Sign -> T -> T -> SProp
:= Signed (fun t1' t2' => AndS (eqS t1 t1') (eqS t2 t2')).

Lemma conj_deciderS {P P': SProp} (pdec: DeciderS P) (pdec': DeciderS P'): DeciderS (AndS P P').
Proof.
  destruct pdec as [ p | np ].
  + destruct pdec' as [ p' | np' ].
    - left.
      split; assumption.
    - right.
      intros [ _ p' ].
      auto.
  + right.
    intros [ p _ ].
    auto.
Qed.

(* Nearly every iteration of the loop proceeds by taking a constraint off of the worklist, adding that constraint to the processed set, and then updating the remaining data structures appropriately (supposing no inconsistency was found).
 * The key word here is "appropriately".
 * In particular, all constraints that were DerivedWithin-able should either be the newly processed constraint or should still be DerivedWithin-able.
 * The following establishes the key cases that must be shown to hold after the update in order to ensure this.
 *)
Lemma process_derived_within
      {Interface_SSet: SSet scheme.(Interface)}
      {IParameter_SubCountable: forall interface: scheme.(Interface), SubCountable (scheme.(IParameter) interface)}
      {Transitive: Sort}
      {Transitive_SubCountable: SubCountableSort Transitive}
      {core: GraphicalCore Transitive}
      {core_Finite: FiniteGraphicalCore core}
      {configuration: Configuration core}
      {processed: IPairSet gcapath gcapath}
      {lower upper: GCAtom core}
      {processed': IPairSet gcapath gcapath}
      {W W': GCAtom core -> GCAtom core -> SProp}
      {L L' U U': GCTransitive core -> GCAtom core -> SProp}
    : IPSExtends processed lower upper processed'
   -> GCAActivatedS (chistory configuration) lower
   -> GCAActivatedS (chistory configuration) upper
   -> (forall atom atom': GCAtom core, W atom atom' -> OrS (AndS (eqS lower atom) (eqS upper atom')) (W' atom atom'))
   -> (forall transitive: GCTransitive core, forall atom: GCAtom core, L transitive atom -> L' transitive atom)
   -> (forall transitive: GCTransitive core, forall atom: GCAtom core, U transitive atom -> U' transitive atom)
   -> (forall transitive': GCTransitive core, forall atom'': GCAtom core, eqS upper (gcatransitive transitive') -> DerivedWithin (chistory configuration) (IPSContains processed') W' L' U' (gcatransitive transitive') atom'' -> OrS (eqS upper atom'') (DerivedWithinStep (chistory configuration) (IPSContains processed') W' L' U' lower atom''))
   -> (forall atom: GCAtom core, forall transitive': GCTransitive core, DerivedWithin (chistory configuration) (IPSContains processed') W' L' U' atom (gcatransitive transitive') -> eqS lower (gcatransitive transitive') -> OrS (eqS lower atom) (DerivedWithinStep (chistory configuration) (IPSContains processed') W' L' U' atom upper))
   -> (forall atom: GCAtom core, forall transitive': GCTransitive core, GCAActivatedS (chistory configuration) atom -> L transitive' atom -> eqS lower (gcatransitive transitive') -> OrS (eqS lower atom) (DerivedWithinStep (chistory configuration) (IPSContains processed') W' L' U' atom upper))
   -> (forall transitive': GCTransitive core, forall atom'': GCAtom core, GCAActivatedS (chistory configuration) atom'' -> eqS upper (gcatransitive transitive') -> U transitive' atom'' -> OrS (eqS upper atom'') (DerivedWithinStep (chistory configuration) (IPSContains processed') W' L' U' lower atom''))
   -> (forall node node': GCNNode core, forall e: eqS (gcnninterface node) (gcnninterface node'), forall parameter: scheme.(IParameter) (gcnninterface node), eqS lower (gcaconcrete (gccnode node)) -> eqS upper (gcaconcrete (gccnode node')) -> OrS (SignedPairEqS lower upper ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument node parameter)) (apply_elimination (gcatomize core) (gcnnargument node' (convert e scheme.(IParameter) parameter)))) (Signed (DerivedWithinStep (chistory configuration) (IPSContains processed') W' L' U') ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument node parameter)) (apply_elimination (gcatomize core) (gcnnargument node' (convert e scheme.(IParameter) parameter)))))
   -> (forall node: GCNNode core, forall listener': GCNListener core, forall interface': scheme.(Interface), forall hkeyed': GCNHKeyedS (chistory configuration) listener' interface', forall e: eqS (gcnninterface node) interface', forall parameter: scheme.(IParameter) (gcnninterface node), eqS lower (gcaconcrete (gccnode node)) -> eqS upper (gcaconcrete (gcclistener listener')) -> OrS (SignedPairEqS lower upper ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument node parameter)) (gcatransitive (gctntransitive (gcntlargument listener' interface' (gcnhkeyed hkeyed') (convert e scheme.(IParameter) parameter))))) (Signed (DerivedWithinStep (chistory configuration) (IPSContains processed') W' L' U') ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument node parameter)) (gcatransitive (gctntransitive (gcntlargument listener' interface' (gcnhkeyed hkeyed') (convert e scheme.(IParameter) parameter))))))
   -> forall atom atom': GCAtom core,
      DerivedWithin (chistory configuration) (IPSContains processed) W L U atom atom'
   -> OrS (AndS (eqS lower atom) (eqS upper atom'))
          (DerivedWithin (chistory configuration) (IPSContains processed') W' L' U' atom atom').
Proof.
  intros extends lactivated uactivated wprocess ll' uu' uderived derivedl transl utrans nnprocess nlprocess.
  apply (DerivedWithin_sind (fun atom atom' => OrS (AndS (eqS lower atom) (eqS upper atom')) (DerivedWithin (chistory configuration) (IPSContains processed') W' L' U' atom atom'))
                            (fun atom atom' => GCAActivatedS (chistory configuration) atom -> GCAActivatedS (chistory configuration) atom' -> OrS (AndS (eqS lower atom) (eqS upper atom')) (DerivedWithinStep (chistory configuration) (IPSContains processed') W' L' U' atom atom'))
                            (fun sign atom atom' => OrS (SignedPairEqS lower upper sign atom atom') (Signed (DerivedWithinStep (chistory configuration) (IPSContains processed') W' L' U') sign atom atom'))).
  + intros atom atom' activated activated' nprocessed _ [ e | derived ]; try assumption; [ left; assumption | ].
    destruct (conj_deciderS (gcaeq_deciderS lower atom lactivated activated) (gcaeq_deciderS upper atom' uactivated activated')) as [ e | ne ]; [ left; assumption | ].
    right.
    apply dwstep; try assumption.
    intro contains'.
    apply (ipscontains_extends extends) in contains'.
    destruct contains' as [ [ eatom eatom' ] | contains ]; try auto.
    eapply gcapath_injS in eatom; try eassumption.
    eapply gcapath_injS in eatom'; try eassumption.
    apply ne.
    split; assumption.
  + intros atom atom' _ [ e | derived ]; [ left; assumption | ].
    right.
    assumption.
  + intros atom atom' _ [ e | derived ]; [ left; assumption | ].
    right.
    assumption.
  + intros atom atom' work _ _.
    apply wprocess in work.
    destruct work as [ e | work' ]; [ left; assumption | ].
    right.
    apply dwwork.
    assumption.
  + intros constraint activated _ _.
    right.
    apply dwconstraint.
    assumption.
  + intros atom transitive' atom'' _ [ [ eatom eupper ] | derived ] _ [ [ elower eatom'' ] | derived' ].
    - left.
      split; assumption.
    - destruct eatom.
      apply uderived in derived'; try assumption.
      destruct derived' as [ e | derived' ]; [ left; split; [ reflexivity | assumption ] | ].
      right.
      assumption.
    - destruct eatom''.
      apply derivedl in derived; try assumption.
      destruct derived as [ e | derived ]; [ left; split; [ assumption | reflexivity ] | ].
      right.
      assumption.
    - right.
      apply dwtransitive with transitive'; assumption.
  + intros atom transitive' atom'' l _ [ [ elower eatom'' ] | derived' ] activated activated''.
    - apply transl in l; try assumption.
      destruct l as [ e | derived ]; [ left; split; assumption | ].
      right.
      destruct eatom''.
      assumption.
    - right.
      apply dwlower with transitive'; auto.
  + intros atom transitive' atom'' _ [ [ eatom eupper ] | derived ] u activated activated''.
    - apply utrans in u; try assumption.
      destruct u as [ e | derived ]; [ left; split; assumption | ].
      right.
      destruct eatom.
      assumption.
    - right.
      apply dwupper with transitive'; auto.
  + intros node node' e parameter _ [ [ elower eupper ] | derived ].
    - destruct (nnprocess node node' e parameter) as [ e' | derived ]; try assumption; [ left; assumption | ].
      right.
      assumption.
    - right.
      apply sderivedwithinstep_signed.
      apply dwnode.
      assumption.
  + intros node listener' interface' hkeyed' e parameter _ [ [ elower eupper ] | derived ].
    - destruct (nlprocess node listener' interface' hkeyed' e parameter) as [ e' | derived ]; try assumption; [ left; assumption | ].
      right.
      assumption.
    - right.
      apply sderivedwithinstep_signed.
      apply dwlistener.
      assumption.
Qed.



(* Part 10.2: The Main Loop *)

Definition spair {T: Type} (sign: Sign) (t t': T): prod T T
:= match sign with
   | negative => pair t' t
   | positive => pair t t'
   end.

(* The following is the core loop of the algorithm for deciding graphical-core consistency.
 * It is the closest analog to Lemma 8.3 of the paper, though the loop here interleaves configuration-refinement and constraint-derivation in order to accommodate more general graphical cores, rather than stages them as in the paper.
 * Rather than return a bool, it returns a SumBoolS indicating whether the inputs are consistent or inconsistent.
 * This enables us to interleave the algorithm implementation with its proof of correctness, which we do because the implementation's proof of termination is highly interleaved with its proof of correctness.
 * If it were to just return a bool, with a subsequent lemma proving correctness, then the implementation would be clearly tail-recursive.
 * However, while here it is still effectively tail-recursive, after each recursive call we need to transform the proof contained within the SumBoolS.
 *
 * configuration is the current configuration.
 * processed is the set of pairs of activated types that have been processed so far.
 * processed_derived captures the invariant that all these pairs are derivable constraints within the current configuration.
 * lindex maps each activated transitive type to its finite set of processed lower bounds.
 * lindex_processed establishes that all lower bounds in lindex are indeed in processed.
 * processed_lindex establishes that all lower bounds in processed are indeed in lindexed.
 * uindex maps each activated transitive type to its finite set of processed upper bounds.
 * uindex_processed establishes that all upper bounds in uindex are indeed in processed.
 * processed_uindex establishes that all upper bounds in processed are indeed in uindexed.
 * work is the worklist of constraints to be proceesed.
 * work_derived captures the invariant that all these pairs are derivable constraints within the current configuration.
 * constrainted captures the invariant that all activated constraints are either in processed or in work.
 *
 * decide_consistency returns one of two possibilities:
 * Either there is a way to refine the current configuration such that all constraints derivable within the given data structures using the refined configuration are shallowly consistent,
 * or the graphical core cannot be consistent using any final history refining the current configuration.
 *)
Lemma decide_consistency
      {Interface_DecEq: DecEq scheme.(Interface)}
      {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)}
      {Transitive: Sort}
      {Transitive_SubFinite: SubFiniteSort Transitive}
      {core: GraphicalCore Transitive}
      {core_Finite: FiniteGraphicalCore core}
      (configuration: Configuration core)
      (processed: IPairSet (gcapath (core := core)) (gcapath (core := core)))
      (processed_derived: IPSForallS (GCAActivatedS (chistory configuration)) (GCAActivatedS (chistory configuration)) (Derived (chistory configuration)) processed)
      (lindex: IPairSet (gctpath (core := core)) (gcapath (core := core)))
      (lindex_processed: IPSForallS (GCTActivatedS (chistory configuration)) (GCAActivatedS (chistory configuration)) (fun transitive lower => IPSContains processed lower (gcatransitive transitive)) lindex)
      (processed_lindex: forall lower: GCAtom core, forall transitive: GCTransitive core, GCAActivatedS (chistory configuration) lower -> GCTActivatedS (chistory configuration) transitive -> IPSContains processed lower (gcatransitive transitive) -> IPSContains lindex transitive lower)
      (uindex: IPairSet (gctpath (core := core)) (gcapath (core := core)))
      (uindex_processed: IPSForallS (GCTActivatedS (chistory configuration)) (GCAActivatedS (chistory configuration)) (fun transitive upper => IPSContains processed (gcatransitive transitive) upper) uindex)
      (processed_uindex: forall transitive: GCTransitive core, forall upper: GCAtom core, GCTActivatedS (chistory configuration) transitive -> GCAActivatedS (chistory configuration) upper -> IPSContains processed (gcatransitive transitive) upper -> IPSContains uindex transitive upper)
      (work: list (prod (GCAtom core) (GCAtom core)))
      (work_derived: ListForallS (fun atoms => Derived (chistory configuration) (fst atoms) (snd atoms)) work)
      (constrained: forall constraint: GCNConstraint core, GCNCActivatedS (chistory configuration) constraint -> OrS (IPSContains processed (apply_elimination (gcatomize core) (gcnclower constraint)) (apply_elimination (gcatomizel core) (gcncupper constraint))) (PairListContains work (apply_elimination (gcatomize core) (gcnclower constraint)) (apply_elimination (gcatomizel core) (gcncupper constraint))))
    : SumBoolS (existsTSS configuration': Configuration core,
                SubConfiguration configuration configuration'
              & forall atom atom': GCAtom core, DerivedWithin (chistory configuration') (IPSContains processed) (PairListContains work) (IPSContains lindex) (IPSContains uindex) atom atom' -> ConsistentGCA (chistory configuration') atom atom'
               )
               (forall history': GCHistory core,
                SubHistory (chistory configuration) history'
             -> FinalGCHistory history'
             -> ConsistentGC history'
             -> FalseS
               ).
Proof.
  assert (forall configuration: Configuration core, forall atom atom': GCAtom core, GCAActivatedS (chistory configuration) atom -> GCAActivatedS (chistory configuration) atom' -> eqS (gcapath atom) (gcapath atom') -> atom = atom') as gcaa_inj by (intros; eapply gcapath_inj; try apply eqS_eq; eassumption).
  assert (forall configuration: Configuration core, forall transitive transitive': GCTransitive core, GCTActivatedS (chistory configuration) transitive -> GCTActivatedS (chistory configuration) transitive' -> eqS (gctpath transitive) (gctpath transitive') -> transitive = transitive') as gcta_inj by (intros; eapply gctpath_inj; try apply eqS_eq; eassumption).
  revert processed processed_derived lindex lindex_processed processed_lindex uindex uindex_processed processed_uindex work work_derived constrained.
  induction (ssc_cwf configuration) as [ configuration _ IHconfiguration ].
  intros processed processed_derived.
  induction (ipairset_cwf (gcatrunk configuration) (gcatrunk configuration) (gcaa_inj configuration) (gcaa_inj configuration) (gcatrunk_contains configuration) (gcatrunk_contains configuration) processed processed_derived) as [ processed _ IHprocessed ]; try (intros atom atom' derived; apply sderived_activated in derived; destruct derived; split; apply gcatrunk_contains; assumption).
  intros lindex lindex_processed processed_lindex uindex uindex_processed processed_uindex work work_derived constrained.
  induction work as [ | [ lower upper ] work IHwork ].
  + left.
    exists configuration; try apply subconfiguration_refl.
    intros atom atom' derived.
    exfalso.
    apply falseS_false.
    apply derivedwithin_processed_false in derived; try assumption.
    - intros constraint activated.
      specialize (constrained constraint activated).
      destruct constrained as [ contained | contained ]; try assumption.
      inversion contained.
    - clear.
      intros atom atom' contains.
      inversion contains.
  + simpl in *.
    destruct work_derived as [ derived work_derived ].
    pose proof (ipsadd_extends processed lower upper) as added.
    destruct (ipsadd processed lower upper) as [ processed' | ].
    - clear IHwork.
      specialize (IHprocessed processed').
      destruct (sderived_activated derived) as [ lactivated uactivated ].
      specialize (IHprocessed (ex_introTSP lower lactivated (ex_introTSP upper (conjS _ _ uactivated derived) added))).
      specialize (IHprocessed (ipsforallS_extend (gcaa_inj configuration) (gcaa_inj configuration) added processed_derived lactivated uactivated derived)).
      destruct lower as [ lower | lower ]; destruct upper as [ upper | upper ].
      * destruct lower as [ lower | lower | ]; try (apply derived_listener_false in derived; destruct derived; fail); destruct upper as [ upper | upper | ].
        ** destruct (decidableS (GCNLKeyedS upper (gcnninterface lower))) as [ keyed | nhkeyed ]; [ pose proof (configuration_set_extends configuration upper uactivated (gcnninterface lower) keyed) as extends; destruct (configuration_set configuration upper uactivated (gcnninterface lower) keyed) as [ [ configuration' | ] | ] | ].
           *** assert (SubConfiguration configuration configuration') as subc by apply (cextends_sub extends).
               assert (IPSForallS (GCAActivatedS (chistory configuration')) (GCAActivatedS (chistory configuration')) (Derived (chistory configuration)) processed) as processed_derived' by (revert processed_derived; apply ipsforallS_mono'; try trivial; apply gcaactivatedS_subhistory; apply subconfiguration_subhistory; assumption).
               pose proof (constraint_extends extends) as [ constraints_activated activated_constraints ].
               destruct IHconfiguration with configuration' processed lindex uindex (cons (pair (gcaconcrete (gccnode lower)) (gcaconcrete (gcclistener upper))) (app (map (fun constraint => pair (apply_elimination (gcatomize core) (gcnclower constraint)) (apply_elimination (gcatomizel core) (gcncupper constraint))) (gcnl_constraints upper (gcnninterface lower) (gcnhkeyed (cextends_chkeyed extends)))) work)) as [ consistent | nconsistent ].
               **** exists upper.
                    exists uactivated.
                    exists (gcnninterface lower).
                    assumption.
               **** revert processed_derived'.
                    apply ipsforallS_mono.
                    intros atom atom' _ _.
                    apply derived_subhistory.
                    apply subconfiguration_subhistory.
                    assumption.
               **** revert lindex_processed.
                    apply ipsforallS_mono'; try (apply gcaactivatedS_subhistory || apply gctactivatedS_subhistory; apply subconfiguration_subhistory; assumption).
                    trivial.
               **** intros atom transitive activated activated' contains.
                    pose proof contains as derived'.
                    apply (ipsforallS_forall (gcaa_inj configuration') (gcaa_inj configuration') processed_derived') in derived'; try assumption.
                    apply sderived_activated in derived'.
                    apply processed_lindex; try apply derived'.
                    assumption.
               **** revert uindex_processed.
                    apply ipsforallS_mono'; try (apply gcaactivatedS_subhistory || apply gctactivatedS_subhistory; apply subconfiguration_subhistory; assumption).
                    trivial.
               **** intros atom transitive activated activated' contains.
                    pose proof contains as derived'.
                    apply (ipsforallS_forall (gcaa_inj configuration') (gcaa_inj configuration') processed_derived') in derived'; try assumption.
                    apply sderived_activated in derived'.
                    apply processed_uindex; try apply derived'.
                    assumption.
               **** split; try apply forall_app.
                    ***** simpl.
                          revert derived.
                          apply derived_subhistory.
                          apply subconfiguration_subhistory.
                          assumption.
                    ***** apply forall_map.
                          revert constraints_activated.
                          apply listforallS_mono.
                          intros constraint activated.
                          apply dconstraint.
                          assumption.
                    ***** revert work_derived.
                          apply listforallS_mono.
                          intros [ atom atom' ].
                          eapply derived_subhistory.
                          apply subconfiguration_subhistory.
                          assumption.
               **** intros constraint activated.
                    apply activated_constraints in activated.
                    destruct activated as [ activated | contains ].
                    ***** apply constrained in activated.
                          destruct activated as [ contains | contains ].
                          ****** left.
                                 assumption.
                          ****** right.
                                 inversion_hset contains.
                                 ******* apply lchead.
                                 ******* apply lctail.
                                         apply contains_app_r.
                                         assumption.
                    ***** right.
                          apply lctail.
                          apply contains_app_l.
                          apply (contains_map (fun constraint => pair (apply_elimination (gcatomize core) (gcnclower constraint)) (apply_elimination (gcatomizel core) (gcncupper constraint)))).
                          assumption.
               **** left.
                    destruct consistent as [ configuration'' sub' consistent ].
                    exists configuration''; try (apply subconfiguration_trans with configuration'; assumption).
                    clear derived.
                    intros atom atom' derived.
                    apply consistent.
                    revert atom atom' derived.
                    apply derivedwithin_mono; try trivial.
                    intros atom atom' contains.
                    inversion_hset contains.
                    ***** apply lchead.
                    ***** apply lctail.
                          apply contains_app_r.
                          assumption.
               **** right.
                    intros history' subh final' consistent'.
                    apply nconsistent with history'; try assumption.
                    intros listener interface hkeyed.
                    apply (chkeyed_extends extends) in hkeyed.
                    destruct hkeyed as [ [ el ei ] | hkeyed ].
                    ***** destruct el.
                          destruct ei.
                          apply (derived_subhistory subh) in derived.
                          apply consistent' in derived.
                          assumption.
                    ***** apply subh.
                          assumption.
           *** destruct extends as [ hkeyed ].
               destruct IHprocessed with lindex uindex (app (flist (fun parameter => spair ((hierarchy.(hinterface) (gcnninterface lower)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument lower parameter)) (gcatransitive (gctntransitive (gcntlargument upper (gcnninterface lower) keyed parameter))))) work) as [ consistent | nconsistent ].
               **** eapply ipsforallS_mono; try apply lindex_processed.
                    simpl.
                    intros transitive lower' _ _ contains.
                    apply (ipsextends_contains added).
                    assumption.
               **** intros lower' transitive activated activated' contains.
                    apply processed_lindex; try assumption.
                    apply (ipscontains_extends added) in contains.
                    destruct contains as [ [ elower eupper ] | contains ]; try assumption.
                    inversion eupper.
               **** eapply ipsforallS_mono; try apply uindex_processed.
                    simpl.
                    intros transitive upper' _ _ contains.
                    apply (ipsextends_contains added).
                    assumption.
               **** intros transitive upper' activated activated' contains.
                    apply processed_uindex; try assumption.
                    apply (ipscontains_extends added) in contains.
                    destruct contains as [ [ elower eupper ] | contains ]; try assumption.
                    inversion elower.
               **** apply forall_app; try assumption.
                    apply flist_forall.
                    intro parameter.
                    apply (dlistener _ _ _ hkeyed (eqS_refl _) parameter) in derived.
                    apply sderived_signed in derived.
                    rewrite convert_id in derived.
                    destruct ((hierarchy.(hinterface) (gcnninterface lower)).(uisvariance) parameter); assumption.
               **** intros constraint activated.
                    specialize (constrained constraint activated).
                    destruct constrained as [ constrained | constrained ]; [ | inversion_hset constrained ].
                    ***** left.
                          apply (ipsextends_contains added).
                          assumption.
                    ***** left.
                          rewrite H0.
                          rewrite H1.
                          apply (ipsextends_contains_pair added).
                    ***** right.
                          apply contains_app_r.
                          assumption.
               **** left.
                    destruct consistent as [ configuration' subc consistent ].
                    exists configuration'; try assumption.
                    clear derived.
                    intros atom atom' derived.
                    eapply (process_derived_within added) in derived; try clear atom atom' derived.
                    ***** destruct derived as [ [ eatom eatom' ] | derived ].
                          ****** destruct eatom.
                                 destruct eatom'.
                                 simpl.
                                 apply (subconfiguration_subhistory subc).
                                 assumption.
                          ****** apply consistent in derived.
                                 assumption.
                    ***** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
                          assumption.
                    ***** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
                          assumption.
                    ***** intros atom atom' contains.
                          inversion_hset contains; try (left; split; reflexivity).
                          right.
                          apply contains_app_r.
                          assumption.
                    ***** trivial.
                    ***** trivial.
                    ***** intros transitive' atom'' e derived'.
                          inversion e.
                    ***** intros atom transitive' derived e.
                          inversion e.
                    ***** intros atom transitive' activated l e.
                          inversion e.
                    ***** intros transitive' atom'' activated'' e u.
                          inversion e.
                    ***** intros node node' e parameter elower eupper.
                          inversion eupper.
                    ***** intros node listener' interface' hkeyed' e parameter elower eupper.
                          right.
                          inversion_hset elower.
                          inversion_hset eupper.
                          destruct e.
                          rewrite convert_id.
                          eapply signed_mono; try apply dwwork.
                          remember ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) as variance.
                          destruct variance; apply contains_app_l; simpl.
                          ****** fold (spair negative (apply_elimination (gcatomize core) (gcnnargument node parameter)) (gcatransitive (gctntransitive (gcntlargument listener' (gcnninterface node) (gcnhkeyed hkeyed') parameter)))).
                                 rewrite Heqvariance.
                                 apply contains_flist with (f := fun parameter => spair ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument node parameter)) (gcatransitive (gctntransitive (gcntlargument listener' (gcnninterface node) (gcnhkeyed hkeyed') parameter)))).
                          ****** fold (spair positive (apply_elimination (gcatomize core) (gcnnargument node parameter)) (gcatransitive (gctntransitive (gcntlargument listener' (gcnninterface node) (gcnhkeyed hkeyed') parameter)))).
                                 rewrite Heqvariance.
                                 apply contains_flist with (f := fun parameter => spair ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument node parameter)) (gcatransitive (gctntransitive (gcntlargument listener' (gcnninterface node) (gcnhkeyed hkeyed') parameter)))).
               **** right.
                    assumption.
           *** right.
               destruct extends as [ interface' [ hkeyed' ] ne ].
               intros history' subc final' consistent'.
               exfalso.
               apply ne.
               apply (derived_subhistory subc) in derived.
               apply consistent' in derived.
               apply eqS_eq.
               eapply fgcnhunique with upper; try eassumption.
               apply subc.
               assumption.
           *** right.
               intros history' subc final' consistent'.
               apply nhkeyed.
               apply (derived_subhistory subc) in derived.
               apply consistent' in derived.
               eapply gcnhkeyed.
               eassumption.
        ** destruct (decidableS (eqS (gcnninterface lower) (gcnninterface upper))) as [ einterface | neinterface ].
           *** destruct IHprocessed with lindex uindex (app (flist (fun parameter => spair ((hierarchy.(hinterface) (gcnninterface lower)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument lower parameter)) (apply_elimination (gcatomize core) (gcnnargument upper (convert einterface scheme.(IParameter) parameter))))) work) as [ consistent | nconsistent ].
               **** eapply ipsforallS_mono; try apply lindex_processed.
                    simpl.
                    intros transitive lower' _ _ contains.
                    apply (ipsextends_contains added).
                    assumption.
               **** intros lower' transitive activated activated' contains.
                    apply processed_lindex; try assumption.
                    apply (ipscontains_extends added) in contains.
                    destruct contains as [ [ elower eupper ] | contains ]; try assumption.
                    inversion eupper.
               **** eapply ipsforallS_mono; try apply uindex_processed.
                    simpl.
                    intros transitive upper' _ _ contains.
                    apply (ipsextends_contains added).
                    assumption.
               **** intros transitive upper' activated activated' contains.
                    apply processed_uindex; try assumption.
                    apply (ipscontains_extends added) in contains.
                    destruct contains as [ [ elower eupper ] | contains ]; try assumption.
                    inversion elower.
               **** apply forall_app; try assumption.
                    apply flist_forall.
                    intro parameter.
                    apply (dnode _ _ einterface parameter) in derived.
                    apply sderived_signed in derived.
                    destruct ((hierarchy.(hinterface) (gcnninterface lower)).(uisvariance) parameter); assumption.
               **** intros constraint activated.
                    specialize (constrained constraint activated).
                    destruct constrained as [ constrained | constrained ]; [ | inversion_hset constrained ].
                    ***** left.
                          apply (ipsextends_contains added).
                          assumption.
                    ***** left.
                          rewrite H0.
                          rewrite H1.
                          apply (ipsextends_contains_pair added).
                    ***** right.
                          apply contains_app_r.
                          assumption.
               **** left.
                    destruct consistent as [ configuration' subc consistent ].
                    exists configuration'; try assumption.
                    clear derived.
                    intros atom atom' derived.
                    eapply (process_derived_within added) in derived; try clear atom atom' derived.
                    ***** destruct derived as [ [ eatom eatom' ] | derived ].
                          ****** destruct eatom.
                                 destruct eatom'.
                                 assumption.
                          ****** apply consistent in derived.
                                 assumption.
                    ***** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
                          assumption.
                    ***** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
                          assumption.
                    ***** intros atom atom' contains.
                          inversion_hset contains; try (left; split; reflexivity).
                          right.
                          apply contains_app_r.
                          assumption.
                    ***** trivial.
                    ***** trivial.
                    ***** intros transitive' atom'' e derived'.
                          inversion e.
                    ***** intros atom transitive' derived e.
                          inversion e.
                    ***** intros atom transitive' activated l e.
                          inversion e.
                    ***** intros transitive' atom'' activated'' e u.
                          inversion e.
                    ***** intros node node' e parameter elower eupper.
                          right.
                          inversion_hset elower.
                          inversion_hset eupper.
                          merge e einterface.
                          eapply signed_mono; try apply dwwork.
                          remember ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) as variance.
                          destruct variance; apply contains_app_l; simpl.
                          ****** fold (spair negative (apply_elimination (gcatomize core) (gcnnargument node parameter)) (apply_elimination (gcatomize core) (gcnnargument node' (convert e scheme.(IParameter) parameter)))).
                                 rewrite Heqvariance.
                                 apply contains_flist with (f := fun parameter => spair ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument node parameter)) (apply_elimination (gcatomize core) (gcnnargument node' (convert e scheme.(IParameter) parameter)))).
                          ****** fold (spair positive (apply_elimination (gcatomize core) (gcnnargument node parameter)) (apply_elimination (gcatomize core) (gcnnargument node' (convert e scheme.(IParameter) parameter)))).
                                 rewrite Heqvariance.
                                 apply contains_flist with (f := fun parameter => spair ((hierarchy.(hinterface) (gcnninterface node)).(uisvariance) parameter) (apply_elimination (gcatomize core) (gcnnargument node parameter)) (apply_elimination (gcatomize core) (gcnnargument node' (convert e scheme.(IParameter) parameter)))).
                    ***** intros node listener' interface' hkeyed' e parameter elower eupper.
                          inversion eupper.
               **** right.
                    assumption.
           *** right.
               intros history' sub final consistent.
               apply (derived_subhistory sub) in derived.
               apply consistent in derived.
               apply neinterface.
               assumption.
        ** destruct IHprocessed with lindex uindex work as [ consistent | nconsistent ].
           *** eapply ipsforallS_mono; try apply lindex_processed.
               simpl.
               intros transitive lower' _ _ contains.
               apply (ipsextends_contains added).
               assumption.
           *** intros lower' transitive activated activated' contains.
               apply processed_lindex; try assumption.
               apply (ipscontains_extends added) in contains.
               destruct contains as [ [ elower eupper ] | contains ]; try assumption.
               inversion eupper.
           *** eapply ipsforallS_mono; try apply uindex_processed.
               simpl.
               intros transitive upper' _ _ contains.
               apply (ipsextends_contains added).
               assumption.
           *** intros transitive upper' activated activated' contains.
               apply processed_uindex; try assumption.
               apply (ipscontains_extends added) in contains.
               destruct contains as [ [ elower eupper ] | contains ]; try assumption.
               inversion elower.
           *** assumption.
           *** intros constraint activated.
               specialize (constrained constraint activated).
               destruct constrained as [ constrained | constrained ]; [ | inversion_hset constrained ].
               **** left.
                    apply (ipsextends_contains added).
                    assumption.
               **** left.
                    rewrite H0.
                    rewrite H1.
                    apply (ipsextends_contains_pair added).
               **** right.
                    assumption.
           *** left.
               destruct consistent as [ configuration' subc consistent ].
               exists configuration'; try assumption.
               clear derived.
               intros atom atom' derived.
               eapply (process_derived_within added) in derived; try clear atom atom' derived.
               **** destruct derived as [ [ eatom eatom' ] | derived ].
                    ***** destruct eatom.
                          destruct eatom'.
                          split.
                    ***** apply consistent in derived.
                          assumption.
               **** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
                    assumption.
               **** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
                    assumption.
               **** intros atom atom' contains.
                    inversion_hset contains; try (left; split; reflexivity).
                    right.
                    assumption.
               **** trivial.
               **** trivial.
               **** intros transitive' atom'' e derived'.
                    inversion e.
               **** intros atom transitive' derived e.
                    inversion e.
               **** intros atom transitive' activated l e.
                    inversion e.
               **** intros transitive' atom'' activated'' e u.
                    inversion e.
               **** intros node node' e parameter elower eupper.
                    inversion eupper.
               **** intros node listener' interface' hkeyed' e parameter elower eupper.
                    inversion eupper.
           *** right.
               assumption.
        ** right.
           intros history' subc final' consistent'.
           apply (derived_subhistory subc) in derived.
           apply consistent' in derived.
           assumption.
        ** right.
           intros history' subc final' consistent'.
           apply (derived_subhistory subc) in derived.
           apply consistent' in derived.
           assumption.
        ** destruct IHprocessed with lindex uindex work as [ consistent | nconsistent ].
           *** eapply ipsforallS_mono; try apply lindex_processed.
               simpl.
               intros transitive lower' _ _ contains.
               apply (ipsextends_contains added).
               assumption.
           *** intros lower' transitive activated activated' contains.
               apply processed_lindex; try assumption.
               apply (ipscontains_extends added) in contains.
               destruct contains as [ [ elower eupper ] | contains ]; try assumption.
               inversion eupper.
           *** eapply ipsforallS_mono; try apply uindex_processed.
               simpl.
               intros transitive upper' _ _ contains.
               apply (ipsextends_contains added).
               assumption.
           *** intros transitive upper' activated activated' contains.
               apply processed_uindex; try assumption.
               apply (ipscontains_extends added) in contains.
               destruct contains as [ [ elower eupper ] | contains ]; try assumption.
               inversion elower.
           *** assumption.
           *** intros constraint activated.
               specialize (constrained constraint activated).
               destruct constrained as [ constrained | constrained ]; [ | inversion_hset constrained ].
               **** left.
                    apply (ipsextends_contains added).
                    assumption.
               **** left.
                    rewrite H1.
                    rewrite H0.
                    apply (ipsextends_contains_pair added).
               **** right.
                    assumption.
           *** left.
               destruct consistent as [ configuration' subc consistent ].
               exists configuration'; try assumption.
               clear derived.
               intros atom atom' derived.
               eapply (process_derived_within added) in derived; try clear atom atom' derived.
               **** destruct derived as [ [ eatom eatom' ] | derived ].
                    ***** destruct eatom.
                          destruct eatom'.
                          split.
                    ***** apply consistent in derived.
                          assumption.
               **** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
                    assumption.
               **** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
                    assumption.
               **** intros atom atom' contains.
                    inversion_hset contains; try (left; split; reflexivity).
                    right.
                    assumption.
               **** trivial.
               **** trivial.
               **** intros transitive' atom'' e derived'.
                    inversion e.
               **** intros atom transitive' derived e.
                    inversion e.
               **** intros atom transitive' activated l e.
                    inversion e.
               **** intros transitive' atom'' activated'' e u.
                    inversion e.
               **** intros node node' e parameter elower eupper.
                    inversion eupper.
               **** intros node listener' interface' hkeyed' e parameter elower eupper.
                    inversion eupper.
           *** right.
               assumption.
      * pose proof (ipsadd_extends lindex upper (gcaconcrete lower)) as ladded.
        destruct (ipsadd lindex upper (gcaconcrete lower)) as [ lindex' | ]; [ | exfalso; destruct ladded as [ lcontains ]; apply (ipsextends_ncontains added); apply (ipsforallS_forall (gcta_inj configuration) (gcaa_inj configuration) lindex_processed) in lcontains; try assumption; unfold IPSContains in lcontains; unfold ISContains in lcontains; unfold IMContains in lcontains; unfold imget_contained in lcontains; simpl in lcontains; destruct lcontains as [ ? e [ ? e' ? ] ]; destruct e; destruct e'; assumption ].
        destruct IHprocessed with lindex' uindex (app (map (fun upper' => pair (gcaconcrete lower) upper') (ipsget_values uindex upper)) work) as [ consistent | nconsistent ].
        ** apply (ipsforallS_extend (gcta_inj configuration) (gcaa_inj configuration) ladded); try assumption.
           *** revert lindex_processed.
               apply ipsforallS_mono.
               intros atom atom' _ _.
               apply (ipsextends_contains added).
           *** apply (ipsextends_contains_pair added).
        ** intros atom atom' activated activated' contains.
           apply (ipscontains_extends added) in contains.
           destruct contains as [ [ eatom eatom' ] | contains ].
           *** apply (gcapath_injS configuration) in eatom; try assumption.
               destruct eatom.
               apply (gcapath_injS configuration) in eatom'; try assumption.
               symmetry in eatom'.
               inversion_hset eatom'.
               apply (ipsextends_contains_pair ladded).
          *** apply (ipsextends_contains ladded).
              apply processed_lindex; assumption.
        ** eapply ipsforallS_mono; try apply uindex_processed.
           simpl.
           intros transitive upper' _ _ contains.
           apply (ipsextends_contains added).
           assumption.
        ** intros transitive upper' activated activated' contains.
           apply processed_uindex; try assumption.
           apply (ipscontains_extends added) in contains.
           destruct contains as [ [ elower eupper ] | contains ]; try assumption.
           inversion elower.
        ** apply forall_app; try assumption.
           apply forall_map.
           simpl.
           apply forall_listforallS.
           intros atom' contains'.
           apply (ipscontains_values uindex_processed) in contains'; try assumption.
           destruct contains' as [ activated' contains' ].
           apply (ipsforallS_forall (gcta_inj configuration) (gcaa_inj configuration) uindex_processed) in contains'; try assumption.
           apply (ipsforallS_forall (gcaa_inj configuration) (gcaa_inj configuration) processed_derived) in contains'; try assumption.
           apply dtransitive with upper; try assumption.
        ** intros constraint activated.
           specialize (constrained constraint activated).
           destruct constrained as [ constrained | constrained ]; [ | inversion_hset constrained ].
           *** left.
               apply (ipsextends_contains added).
               assumption.
           *** left.
               rewrite H0.
               rewrite H1.
               apply (ipsextends_contains_pair added).
           *** right.
               apply contains_app_r.
               assumption.
        ** left.
           destruct consistent as [ configuration' subc consistent ].
           exists configuration'; try assumption.
           clear derived.
           intros atom atom' derived.
           eapply (process_derived_within added) in derived; try clear atom atom' derived.
           *** destruct derived as [ [ eatom eatom' ] | derived ].
                ***** destruct eatom.
                      destruct eatom'.
                      split.
                ***** apply consistent in derived.
                      assumption.
           *** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
               assumption.
           *** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
               assumption.
           *** intros atom atom' contains.
               inversion_hset contains; try (left; split; reflexivity).
               right.
               apply contains_app_r.
               assumption.
           *** intros transitive atom.
               apply (ipsextends_contains ladded).
           *** trivial.
           *** intros transitive' atom'' e derived'.
               right.
               symmetry in e.
               inversion_hset e.
               apply dwlower with upper; try assumption.
               apply (ipsextends_contains_pair ladded).
           *** intros atom transitive' derived e.
               inversion e.
           *** intros atom transitive' activated l e.
               inversion e.
           *** intros transitive' atom'' activated'' e u.
               right.
               symmetry in e.
               inversion_hset e.
               apply dwwork.
               apply contains_app_l.
               apply contains_map.
               assert (IPSForallS (GCTActivatedS (chistory configuration')) (GCAActivatedS (chistory configuration')) (fun transitive upper => IPSContains processed (gcatransitive transitive) upper) uindex) as uindex_processed' by (revert uindex_processed; apply ipsforallS_mono'; try trivial; apply gcaactivatedS_subhistory || apply gctactivatedS_subhistory; apply subconfiguration_subhistory; assumption).
               apply (ipsvalues_contains (gcta_inj configuration') (gcaa_inj configuration') uindex_processed'); try assumption.
               apply (gctactivatedS_subhistory (subconfiguration_subhistory subc)).
               assumption.
           *** intros node node' e parameter elower eupper.
               inversion eupper.
           *** intros node listener' interface' hkeyed' e parameter elower eupper.
               inversion eupper.
        ** right.
           assumption.
      * pose proof (ipsadd_extends uindex lower (gcaconcrete upper)) as uadded.
        destruct (ipsadd uindex lower (gcaconcrete upper)) as [ uindex' | ]; [ | exfalso; destruct uadded as [ ucontains ]; apply (ipsextends_ncontains added); apply (ipsforallS_forall (gcta_inj configuration) (gcaa_inj configuration) uindex_processed) in ucontains; try assumption; unfold IPSContains in ucontains; unfold ISContains in ucontains; unfold IMContains in ucontains; unfold imget_contained in ucontains; simpl in ucontains; destruct ucontains as [ ? e [ ? e' ? ] ]; destruct e; destruct e'; assumption ].
        destruct IHprocessed with lindex uindex' (app (map (fun lower' => pair lower' (gcaconcrete upper)) (ipsget_values lindex lower)) work) as [ consistent | nconsistent ].
        ** eapply ipsforallS_mono; try apply lindex_processed.
           simpl.
           intros transitive lower' _ _ contains.
           apply (ipsextends_contains added).
           assumption.
        ** intros transitive lower' activated activated' contains.
           apply processed_lindex; try assumption.
           apply (ipscontains_extends added) in contains.
           destruct contains as [ [ elower eupper ] | contains ]; try assumption.
           inversion eupper.
        ** apply (ipsforallS_extend (gcta_inj configuration) (gcaa_inj configuration) uadded); try assumption.
           *** revert uindex_processed.
               apply ipsforallS_mono.
               intros atom atom' _ _.
               apply (ipsextends_contains added).
           *** apply (ipsextends_contains_pair added).
        ** intros atom atom' activated activated' contains.
           apply (ipscontains_extends added) in contains.
           destruct contains as [ [ eatom eatom' ] | contains ].
           *** apply (gcapath_injS configuration) in eatom; try assumption.
               apply (gcapath_injS configuration) in eatom'; try assumption.
               destruct eatom'.
               symmetry in eatom.
               inversion_hset eatom.
               apply (ipsextends_contains_pair uadded).
          *** apply (ipsextends_contains uadded).
              apply processed_uindex; assumption.
        ** apply forall_app; try assumption.
           apply forall_map.
           simpl.
           apply forall_listforallS.
           intros atom' contains'.
           apply (ipscontains_values lindex_processed) in contains'; try assumption.
           destruct contains' as [ activated' contains' ].
           apply (ipsforallS_forall (gcta_inj configuration) (gcaa_inj configuration) lindex_processed) in contains'; try assumption.
           apply (ipsforallS_forall (gcaa_inj configuration) (gcaa_inj configuration) processed_derived) in contains'; try assumption.
           apply dtransitive with lower; try assumption.
        ** intros constraint activated.
           specialize (constrained constraint activated).
           destruct constrained as [ constrained | constrained ]; [ | inversion_hset constrained ].
           *** left.
               apply (ipsextends_contains added).
               assumption.
           *** left.
               rewrite H0.
               rewrite H1.
               apply (ipsextends_contains_pair added).
           *** right.
               apply contains_app_r.
               assumption.
        ** left.
           destruct consistent as [ configuration' subc consistent ].
           exists configuration'; try assumption.
           clear derived.
           intros atom atom' derived.
           eapply (process_derived_within added) in derived; try clear atom atom' derived.
           *** destruct derived as [ [ eatom eatom' ] | derived ].
                ***** destruct eatom.
                      destruct eatom'.
                      split.
                ***** apply consistent in derived.
                      assumption.
           *** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
               assumption.
           *** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
               assumption.
           *** intros atom atom' contains.
               inversion_hset contains; try (left; split; reflexivity).
               right.
               apply contains_app_r.
               assumption.
           *** trivial.
           *** intros transitive atom.
               apply (ipsextends_contains uadded).
           *** intros atom transitive' e derived'.
               inversion e.
           *** intros transitive' atom'' derived e.
               right.
               symmetry in e.
               inversion_hset e.
               apply dwupper with lower; try assumption.
               apply (ipsextends_contains_pair uadded).
           *** intros transitive' atom'' activated u e.
               right.
               symmetry in e.
               inversion_hset e.
               apply dwwork.
               apply contains_app_l.
               apply (contains_map (fun lower' => pair lower' (gcaconcrete upper))).
               assert (IPSForallS (GCTActivatedS (chistory configuration')) (GCAActivatedS (chistory configuration')) (fun transitive lower => IPSContains processed lower (gcatransitive transitive)) lindex) as lindex_processed' by (revert lindex_processed; apply ipsforallS_mono'; try trivial; apply gcaactivatedS_subhistory || apply gctactivatedS_subhistory; apply subconfiguration_subhistory; assumption).
               apply (ipsvalues_contains (gcta_inj configuration') (gcaa_inj configuration') lindex_processed'); try assumption.
               apply (gctactivatedS_subhistory (subconfiguration_subhistory subc)).
               assumption.
           *** intros atom transitive' activated'' e l.
               inversion e.
           *** intros node node' e parameter elower eupper.
               inversion elower.
           *** intros node listener' interface' hkeyed' e parameter elower eupper.
               inversion elower.
        ** right.
           assumption.
      * pose proof (ipsadd_extends lindex upper (gcatransitive lower)) as ladded.
        destruct (ipsadd lindex upper (gcatransitive lower)) as [ lindex' | ]; [ | exfalso; destruct ladded as [ lcontains ]; apply (ipsextends_ncontains added); apply (ipsforallS_forall (gcta_inj configuration) (gcaa_inj configuration) lindex_processed) in lcontains; try assumption; unfold IPSContains in lcontains; unfold ISContains in lcontains; unfold IMContains in lcontains; unfold imget_contained in lcontains; simpl in lcontains; destruct lcontains as [ ? e [ ? e' ? ] ]; destruct e; destruct e'; assumption ].
        pose proof (ipsadd_extends uindex lower (gcatransitive upper)) as uadded.
        destruct (ipsadd uindex lower (gcatransitive upper)) as [ uindex' | ]; [ | exfalso; destruct uadded as [ ucontains ]; apply (ipsextends_ncontains added); apply (ipsforallS_forall (gcta_inj configuration) (gcaa_inj configuration) uindex_processed) in ucontains; try assumption; unfold IPSContains in ucontains; unfold ISContains in ucontains; unfold IMContains in ucontains; unfold imget_contained in ucontains; simpl in ucontains; destruct ucontains as [ ? e [ ? e' ? ] ]; destruct e; destruct e'; assumption ].
        destruct IHprocessed with lindex' uindex' (app (app (map (fun upper' => pair (gcatransitive lower) upper') (ipsget_values uindex upper)) (map (fun lower' => pair lower' (gcatransitive upper)) (ipsget_values lindex lower))) work) as [ consistent | nconsistent ].
        ** apply (ipsforallS_extend (gcta_inj configuration) (gcaa_inj configuration) ladded); try assumption.
           *** revert lindex_processed.
               apply ipsforallS_mono.
               intros atom atom' _ _.
               apply (ipsextends_contains added).
           *** apply (ipsextends_contains_pair added).
        ** intros atom atom' activated activated' contains.
           apply (ipscontains_extends added) in contains.
           destruct contains as [ [ eatom eatom' ] | contains ].
           *** apply (gcapath_injS configuration) in eatom; try assumption.
               destruct eatom.
               apply (gcapath_injS configuration) in eatom'; try assumption.
               symmetry in eatom'.
               inversion_hset eatom'.
               apply (ipsextends_contains_pair ladded).
          *** apply (ipsextends_contains ladded).
              apply processed_lindex; assumption.
        ** apply (ipsforallS_extend (gcta_inj configuration) (gcaa_inj configuration) uadded); try assumption.
           *** revert uindex_processed.
               apply ipsforallS_mono.
               intros atom atom' _ _.
               apply (ipsextends_contains added).
           *** apply (ipsextends_contains_pair added).
        ** intros atom atom' activated activated' contains.
           apply (ipscontains_extends added) in contains.
           destruct contains as [ [ eatom eatom' ] | contains ].
           *** apply (gcapath_injS configuration) in eatom; try assumption.
               apply (gcapath_injS configuration) in eatom'; try assumption.
               destruct eatom'.
               symmetry in eatom.
               inversion_hset eatom.
               apply (ipsextends_contains_pair uadded).
          *** apply (ipsextends_contains uadded).
              apply processed_uindex; assumption.
        ** apply forall_app; try assumption.
           apply forall_app.
           *** apply forall_map.
               simpl.
               apply forall_listforallS.
               intros atom' contains'.
               apply (ipscontains_values uindex_processed) in contains'; try assumption.
               destruct contains' as [ activated' contains' ].
               apply (ipsforallS_forall (gcta_inj configuration) (gcaa_inj configuration) uindex_processed) in contains'; try assumption.
               apply (ipsforallS_forall (gcaa_inj configuration) (gcaa_inj configuration) processed_derived) in contains'; try assumption.
               apply dtransitive with upper; try assumption.
           *** apply forall_map.
               simpl.
               apply forall_listforallS.
               intros atom' contains'.
               apply (ipscontains_values lindex_processed) in contains'; try assumption.
               destruct contains' as [ activated' contains' ].
               apply (ipsforallS_forall (gcta_inj configuration) (gcaa_inj configuration) lindex_processed) in contains'; try assumption.
               apply (ipsforallS_forall (gcaa_inj configuration) (gcaa_inj configuration) processed_derived) in contains'; try assumption.
               apply dtransitive with lower; try assumption.
        ** intros constraint activated.
           specialize (constrained constraint activated).
           destruct constrained as [ constrained | constrained ]; [ | inversion_hset constrained ].
           *** left.
               apply (ipsextends_contains added).
               assumption.
           *** left.
               rewrite H0.
               rewrite H1.
               apply (ipsextends_contains_pair added).
           *** right.
               apply contains_app_r.
               assumption.
        ** left.
           destruct consistent as [ configuration' subc consistent ].
           exists configuration'; try assumption.
           clear derived.
           intros atom atom' derived.
           eapply (process_derived_within added) in derived; try clear atom atom' derived.
           *** destruct derived as [ [ eatom eatom' ] | derived ].
                ***** destruct eatom.
                      destruct eatom'.
                      split.
                ***** apply consistent in derived.
                      assumption.
           *** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
               assumption.
           *** apply (gcaactivatedS_subhistory (subconfiguration_subhistory subc)).
               assumption.
           *** intros atom atom' contains.
               inversion_hset contains; try (left; split; reflexivity).
               right.
               apply contains_app_r.
               assumption.
           *** intros transitive atom.
               apply (ipsextends_contains ladded).
           *** intros transitive atom.
               apply (ipsextends_contains uadded).
           *** intros transitive' atom'' e derived'.
               right.
               symmetry in e.
               inversion_hset e.
               apply dwlower with upper; try assumption.
               apply (ipsextends_contains_pair ladded).
           *** intros transitive' atom'' derived' e.
               right.
               symmetry in e.
               inversion_hset e.
               apply dwupper with lower; try assumption.
               apply (ipsextends_contains_pair uadded).
           *** intros atom transitive' activated l e.
               right.
               symmetry in e.
               inversion_hset e.
               apply dwwork.
               apply contains_app_l.
               apply contains_app_r.
               apply (contains_map (fun lower' => pair lower' (gcatransitive upper))).
               assert (IPSForallS (GCTActivatedS (chistory configuration')) (GCAActivatedS (chistory configuration')) (fun transitive lower => IPSContains processed lower (gcatransitive transitive)) lindex) as lindex_processed' by (revert lindex_processed; apply ipsforallS_mono'; try trivial; apply gcaactivatedS_subhistory || apply gctactivatedS_subhistory; apply subconfiguration_subhistory; assumption).
               apply (ipsvalues_contains (gcta_inj configuration') (gcaa_inj configuration') lindex_processed'); try assumption.
               apply (gctactivatedS_subhistory (subconfiguration_subhistory subc)).
               assumption.
           *** intros transitive' atom'' activated'' e u.
               right.
               symmetry in e.
               inversion_hset e.
               apply dwwork.
               apply contains_app_l.
               apply contains_app_l.
               apply contains_map.
               assert (IPSForallS (GCTActivatedS (chistory configuration')) (GCAActivatedS (chistory configuration')) (fun transitive upper => IPSContains processed (gcatransitive transitive) upper) uindex) as uindex_processed' by (revert uindex_processed; apply ipsforallS_mono'; try trivial; apply gcaactivatedS_subhistory || apply gctactivatedS_subhistory; apply subconfiguration_subhistory; assumption).
               apply (ipsvalues_contains (gcta_inj configuration') (gcaa_inj configuration') uindex_processed'); try assumption.
               apply (gctactivatedS_subhistory (subconfiguration_subhistory subc)).
               assumption.
           *** intros node node' e parameter elower eupper.
               inversion eupper.
           *** intros node listener' interface' hkeyed' e parameter elower eupper.
               inversion eupper.
        ** right.
           assumption.
    - destruct added as [ contains ].
      destruct IHwork as [ consistent | nconsistent ]; try assumption.
      * intros constraint activated.
        specialize (constrained constraint activated).
        destruct constrained as [ constrained | constrained ]; [ | inversion_hset constrained ].
        ** left.
           assumption.
        ** left.
           assumption.
        ** right.
           assumption.
      * left.
        destruct consistent as [ configuration' subc consistent ].
        exists configuration'; try assumption.
        clear derived.
        intros atom atom' derived.
        apply consistent.
        revert atom atom' derived.
        apply (DerivedWithin_sind (DerivedWithin (chistory configuration') (IPSContains processed) (PairListContains work) (IPSContains lindex) (IPSContains uindex)) (fun atom atom' => (IPSContains processed atom atom' -> FalseS) -> DerivedWithinStep (chistory configuration') (IPSContains processed) (PairListContains work) (IPSContains lindex) (IPSContains uindex) atom atom') (SDerivedWithinStep (chistory configuration') (IPSContains processed) (PairListContains work) (IPSContains lindex) (IPSContains uindex))).
        ** intros atom atom' activated activated' nprocessed _ derived.
           specialize (derived nprocessed).
           apply dwstep; assumption.
        ** intros atom atom' _ step _.
           apply dwcontravariant.
           assumption.
        ** intros atom atom' _ step _.
           apply dwcovariant.
           assumption.
        ** intros atom atom' contains' nprocessed.
           inversion_hset contains'.
           *** destruct (nprocessed contains).
           *** apply dwwork.
               assumption.
        ** intros constraint activated _.
           apply dwconstraint.
           assumption.
        ** intros atom transitive' atom'' _ derived _ derived' _.
           apply dwtransitive with transitive'; assumption.
        ** intros atom transitive' atom'' l _ derived' _.
           apply dwlower with transitive'; assumption.
        ** intros atom transitive' atom'' _ derived u _.
           apply dwupper with transitive'; assumption.
        ** intros node node' e parameter _ derived.
           apply dwnode.
           assumption.
        ** intros node listener' interface' hkeyed' e parameter _ derived.
           apply dwlistener.
           assumption.
      * right.
        assumption.
Qed.



(* Part 10.3: Deciding Graphical-Core Consistency
 * The following decides consistency for any finite graphical core, proving Theorem 8.4 of the paper.
 * It first calls the above tail-recursive decider with an empty processed set (and lower- and upper-bound summaries) and the worklist of all trivially activated constraints.
 * Then it transforms either returned proof to show that the result decides consistency of the graphical core.
 *
 * Note that we only need the set of interfaces to have decidability; it does not need to be finite.
 * This leaves room for significantly more kinds of types, such as structural types.
 *)
Theorem ConsistentGC_DecidableS
      {Interface_DecEq: DecEq scheme.(Interface)}
      {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)}
      {Transitive: Sort}
      {Transitive_SubFinite: SubFiniteSort Transitive}
      (core: GraphicalCore Transitive)
      {core_Finite: FiniteGraphicalCore core}
    : DecidableS (existsTS history: GCHistory core, AndS (FinalGCHistory history) (ConsistentGC history)).
Proof.
  assert (SumBoolS (existsTS configuration: Configuration core,
                    forall atom atom': GCAtom core, DerivedWithin (chistory configuration) (IPSContains (ipsempty gcapath gcapath)) (PairListContains (flist (fun constraint: core.(GCConstraint) => pair (apply_elimination (gcatomize core) (gcnclower (gcncconstraint constraint))) (apply_elimination (gcatomizel core) (gcncupper (gcncconstraint constraint)))))) (IPSContains (ipsempty gctpath gcapath)) (IPSContains (ipsempty gctpath gcapath)) atom atom' -> ConsistentGCA (chistory configuration) atom atom'
                   )
                   (forall history: GCHistory core,
                    FinalGCHistory history
                 -> ConsistentGC history
                 -> FalseS
                   )) as [ consistent | nconsistent ].
  + destruct decide_consistency with configuration_empty (ipsempty (gcapath (core := core)) (gcapath (core := core))) (ipsempty (gctpath (core := core)) (gcapath (core := core))) (ipsempty (gctpath (core := core)) (gcapath (core := core))) (flist (fun constraint: core.(GCConstraint) => pair (apply_elimination (gcatomize core) (gcnclower (gcncconstraint constraint))) (apply_elimination (gcatomizel core) (gcncupper (gcncconstraint constraint))))) as [ consistent | nconsistent ].
    - apply ipsforallS_empty.
    - apply ipsforallS_empty.
    - intros lower transitive _ _ contains.
      apply ipsempty_ncontains in contains.
      destruct contains.
    - apply ipsforallS_empty.
    - intros transitive upper _ _ contains.
      apply ipsempty_ncontains in contains.
      destruct contains.
    - apply flist_forall.
      simpl.
      intro constraint.
      apply (dconstraint (gcncconstraint constraint)).
      split.
    - intros constraint activated.
      right.
      destruct constraint; simpl in activated.
      * apply (contains_flist (fun constraint => pair (apply_elimination (gcatomize core) (gcnclower (gcncconstraint constraint))) (apply_elimination (gcatomizel core) (gcncupper (gcncconstraint constraint))))).
      * destruct activated as [ hkeyed activated ].
        cbn in hkeyed.
        destruct hkeyed as [ [ ] _ ].
    - left.
      destruct consistent as [ configuration _ consistent ].
      exists configuration.
      assumption.
    - right.
      intro history.
      apply nconsistent.
      intros listener interface hkeyed.
      apply chkeyed_empty in hkeyed.
      destruct hkeyed.
  + left.
    destruct consistent as [ configuration consistent ].
    exists (chistory configuration).
    split; try apply chistory_final.
    intros atom atom' derived.
    apply consistent.
    revert atom atom' derived.
    apply derived_within with (sign := positive).
    intros atom atom'.
    apply ipsempty_ncontains.
  + right.
    intros [ history [ final consistent ] ].
    apply nconsistent with history; assumption.
Qed.
#[local] Existing Instance ConsistentGC_DecidableS.

(* The following prints only scheme: Scheme and hierarchy: Hierarchy. *)
Print Assumptions ConsistentGC_DecidableS.



(* Part 11: Extraction
 * The following define the graphical care of an expression and prove the construction satisfies the properties in Lemma 9.1 of the paper.
 *)

(* Part 11.1: Syntactic Locations with User Types *)

(* Given a user type "t", the type "Location t" is the set of syntactic locations with "t" that have a corresponding interface. *)
Definition Location {Var: Type}: UserType Var -> Type
:= fix Location (type: UserType Var): Type
:= match type with
   | utvariable _ => Empty
   | utany => Empty
   | utinterface interface arguments => option { parameter: scheme.(IParameter) interface & Location (arguments parameter) }
   end.
(* linterface returns the interface at a given location within a user type. *)
Definition linterface {Var: Type}: forall {type: UserType Var}, Location type -> scheme.(Interface)
:= fix linterface (type: UserType Var): Location type -> scheme.(Interface)
:= match type with
   | utvariable _ => emptye
   | utany => emptye
   | utinterface interface arguments => fun location => match location with
                                                       | None => interface
                                                       | Some (existT _ parameter location) => linterface (arguments parameter) location
                                                       end
   end.
(* ltinterface returns the user types that are the arguments to the interface at the given location within the user type. *)
Definition ltargument {Var: Type}: forall {type: UserType Var}, forall location: Location type, scheme.(IParameter) (linterface location) -> UserType Var
:= fix ltargument {type: UserType Var}: forall location: Location type, scheme.(IParameter) (linterface location) -> UserType Var
:= match type as type return forall location: Location type, scheme.(IParameter) (linterface location) -> UserType Var with
   | utvariable _ => fun e => match e with end
   | utany => fun e => match e with end
   | utinterface interface arguments => fun location => match location as location return scheme.(IParameter) (linterface (type := utinterface interface arguments) location) -> UserType Var with
                                                        | None => arguments
                                                        | Some (existT _ parameter location) => ltargument location
                                                        end
    end.

(* Provided interfaces can have only a Finite number of parameters, there are a subfinite number of locations within any given user type. *)
#[local] Instance Location_SubFinite {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {Var: Type} (type: UserType Var): SubFinite (Location type).
Proof.
  induction type; simpl; apply _.
Qed.

(* tlocation breaks a user type down into the cases Any, a location within the type, or a type variable. *)
Definition tlocation {Var: Type} (type: UserType Var): SumSort (cons Unit (cons (Location type) (cons Var nil)))
:= match type with
   | utvariable variable => sortr (sortr (sortl variable))
   | utany => sortl tt
   | utinterface _ _ => sortr (sortl None)
   end.
(* largument is the composition of tlocation followed by ltinterface, but defined directly in order to facilitate proofs. *)
Definition largument {Var: Type}: forall {type: UserType Var}, forall location: Location type, scheme.(IParameter) (linterface location) -> SumSort (cons Unit (cons (Location type) (cons Var nil)))
:= fix largument {type: UserType Var}: forall location: Location type, scheme.(IParameter) (linterface location) -> SumSort (cons Unit (cons (Location type) (cons Var nil)))
:= match type as type return forall location: Location type, scheme.(IParameter) (linterface location) -> SumSort (cons Unit (cons (Location type) (cons Var nil))) with
   | utvariable _ => fun e => match e with end
   | utany => fun e => match e with end
   | utinterface interface arguments => fun location => match location as location return scheme.(IParameter) (linterface (type := utinterface interface arguments) location) -> SumSort (cons Unit (cons (Location (utinterface interface arguments)) (cons Var nil))) with
                                                        | None => fun parameter => apply_morphism (consid_morphism Unit (cons_morphism (compose (existT _ parameter) Some) id_morphism)) (tlocation (arguments parameter))
                                                        | Some (existT _ parameter location) => fun parameter' => apply_morphism (consid_morphism Unit (cons_morphism (compose (existT _ parameter) Some) id_morphism)) (largument location parameter')
                                                        end
    end.

Lemma tsubst_tlocation {Var: Type} (type: UserType Var) {space: TypeSpace} (substitution: Var -> space.(SpaceType)): tsubst substitution type = apply_elimination (pair_elimination (fun _ => space.(stany)) (pair_elimination (fun location => space.(stinterface) (linterface location) (fun parameter => tsubst substitution (ltargument location parameter))) (pair_elimination substitution nil_elimination))) (tlocation type).
Proof.
  destruct type; reflexivity.
Qed.
Lemma tsubst_ltargument {Var: Type} {type: UserType Var} (location: Location type) (parameter: scheme.(IParameter) (linterface location)) {space: TypeSpace} (substitution: Var -> space.(SpaceType)): tsubst substitution (ltargument location parameter) = apply_elimination (pair_elimination (fun _ => space.(stany)) (pair_elimination (fun location => space.(stinterface) (linterface location) (fun parameter => tsubst substitution (ltargument location parameter))) (pair_elimination substitution nil_elimination))) (largument location parameter).
Proof.
  induction type as [ | | interface arguments IHarguments ]; try (destruct location; fail).
  destruct location as [ [ parameter' location ] | ]; simpl in *.
  + rewrite IHarguments.
    rewrite <- apply_eliminate_morphism.
    reflexivity.
  + rewrite <- apply_eliminate_morphism.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_nil_morphism.
    unfold compose.
    apply tsubst_tlocation.
Qed.

(* Given a user type and a function mapping every location in that user type to a node in a graphical core,
 * if that function maps each location to a node with the same interface and with arguments that correspond in line with a given mapping of the free type variables into a given model,
 * then the model's interpretation of the user type is equivalent to its interpretation of the node. *)
Lemma msubstv
      {Interface_SSet: SSet scheme.(Interface)}
      {Transitive: Sort}
      {core: GraphicalCore Transitive}
      {history: GCHistory core}
      {space: TypeSpace}
      (model: Model history space)
      (elimination: SortElimination space.(SpaceType) Transitive)
      {Var: Type}
      (substitution: SortSelection Var (cons core.(GCAbstract) Transitive))
      (type: UserType Var)
      (node: Location type -> core.(GCNode))
    : ModelV model elimination
   -> forall einterface: forall location: Location type, eqS (linterface location) (core.(gcninterface) (node location)),
      (forall location: Location type, forall parameter: scheme.(IParameter) (linterface location), apply_morphism (consid_morphism Unit (cons_morphism node (pair_morphism substitution nil_morphism))) (largument location parameter) = core.(gcnargument) (node location) (convert (einterface location) scheme.(IParameter) parameter))
   -> AndS (space.(SubSpaceType) (tsubst (compose (apply_selection substitution) (apply_elimination (pair_elimination model.(mabstract) elimination))) type) (apply_elimination (pair_elimination (fun _ => space.(stany)) (pair_elimination (compose node model.(mnode)) (pair_elimination (compose (apply_selection substitution) (apply_elimination (pair_elimination model.(mabstract) elimination))) nil_elimination))) (tlocation type)))
           (space.(SubSpaceType) (apply_elimination (pair_elimination (fun _ => space.(stany)) (pair_elimination (compose node model.(mnode)) (pair_elimination (compose (apply_selection substitution) (apply_elimination (pair_elimination model.(mabstract) elimination))) nil_elimination))) (tlocation type)) (tsubst (compose (apply_selection substitution) (apply_elimination (pair_elimination model.(mabstract) elimination))) type)).
Proof.
  intros vmodel einterface eargument.
  induction type as [ variable | | interface arguments IHarguments ].
  + split; apply sstrefl.
  + split; apply sstrefl.
  + unfold compose.
    specialize (fun parameter => IHarguments parameter (compose (existT _ parameter) (compose Some node)) (fun location => einterface (Some (existT _ parameter location)))); unfold compose in IHarguments.
    split.
    - eapply ssttrans; try apply vmodel.(mlowerv).
      simpl.
      apply sstvariance_eqS with (einterface None).
      simpl.
      intro parameter.
      specialize (IHarguments parameter).
      destruct IHarguments as [ IHarguments IHarguments' ].
      * intros location parameter'.
        specialize (eargument (Some (existT _ parameter location)) parameter').
        cbn in eargument.
        rewrite <- apply_compose_morphism in eargument.
        rewrite compose_consid_consid_morphism in eargument.
        rewrite compose_cons_cons_morphism in eargument.
        rewrite compose_consid_pair_morphism in eargument.
        assumption.
      * specialize (eargument None parameter).
        cbn in eargument.
        rewrite <- apply_compose_morphism in eargument.
        rewrite compose_consid_consid_morphism in eargument.
        rewrite compose_cons_cons_morphism in eargument.
        rewrite compose_consid_pair_morphism in eargument.
        unfold compose in eargument.
        cbn.
        rewrite <- eargument.
        unfold meliminate.
        unfold melimination.
        rewrite <- apply_eliminate_morphism.
        rewrite eliminate_consid_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        rewrite eliminate_pair_morphism.
        rewrite eliminate_nil_morphism.
        unfold compose.
        destruct ((hierarchy.(hinterface) interface).(uisvariance) parameter); assumption.
    - eapply ssttrans; try apply vmodel.(mupperv).
      simpl.
      apply sstvariance_eqS' with (einterface None).
      simpl.
      intro parameter.
      specialize (IHarguments parameter).
      destruct IHarguments as [ IHarguments IHarguments' ].
      * intros location parameter'.
        specialize (eargument (Some (existT _ parameter location)) parameter').
        cbn in eargument.
        rewrite <- apply_compose_morphism in eargument.
        rewrite compose_consid_consid_morphism in eargument.
        rewrite compose_cons_cons_morphism in eargument.
        rewrite compose_consid_pair_morphism in eargument.
        unfold compose in eargument.
        assumption.
      * specialize (eargument None parameter).
        cbn in eargument.
        rewrite <- apply_compose_morphism in eargument.
        rewrite compose_consid_consid_morphism in eargument.
        rewrite compose_cons_cons_morphism in eargument.
        rewrite compose_consid_pair_morphism in eargument.
        unfold compose in eargument.
        cbn.
        rewrite <- eargument.
        unfold meliminate.
        unfold melimination.
        rewrite <- apply_eliminate_morphism.
        rewrite eliminate_consid_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        rewrite eliminate_pair_morphism.
        rewrite eliminate_nil_morphism.
        unfold compose.
        destruct ((hierarchy.(hinterface) interface).(uisvariance) parameter); assumption.
Qed.
Lemma msubstv_lower {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (elimination: SortElimination space.(SpaceType) Transitive) {Var: Type} (substitution: SortSelection Var (cons core.(GCAbstract) Transitive)) (type: UserType Var) (node: Location type -> core.(GCNode)): ModelV model elimination -> forall (einterface: forall location: Location type, eqS (linterface location) (core.(gcninterface) (node location))), (forall location: Location type, forall parameter: scheme.(IParameter) (linterface location), apply_morphism (consid_morphism Unit (cons_morphism node (pair_morphism substitution nil_morphism))) (largument location parameter) = core.(gcnargument) (node location) (convert (einterface location) scheme.(IParameter) parameter)) -> space.(SubSpaceType) (tsubst (compose (apply_selection substitution) (apply_elimination (pair_elimination model.(mabstract) elimination))) type) (apply_elimination (pair_elimination (fun _ => space.(stany)) (pair_elimination (compose node model.(mnode)) (pair_elimination (compose (apply_selection substitution) (apply_elimination (pair_elimination model.(mabstract) elimination))) nil_elimination))) (tlocation type)).
Proof.
  intros.
  eapply msubstv; eassumption.
Qed.
Lemma msubstv_upper {Interface_SSet: SSet scheme.(Interface)} {Transitive: Sort} {core: GraphicalCore Transitive} {history: GCHistory core} {space: TypeSpace} (model: Model history space) (elimination: SortElimination space.(SpaceType) Transitive) {Var: Type} (substitution: SortSelection Var (cons core.(GCAbstract) Transitive)) (type: UserType Var) (node: Location type -> core.(GCNode)): ModelV model elimination -> forall (einterface: forall location: Location type, eqS (linterface location) (core.(gcninterface) (node location))), (forall location: Location type, forall parameter: scheme.(IParameter) (linterface location), apply_morphism (consid_morphism Unit (cons_morphism node (pair_morphism substitution nil_morphism))) (largument location parameter) = core.(gcnargument) (node location) (convert (einterface location) scheme.(IParameter) parameter)) -> space.(SubSpaceType) (apply_elimination (pair_elimination (fun _ => space.(stany)) (pair_elimination (compose node model.(mnode)) (pair_elimination (compose (apply_selection substitution) (apply_elimination (pair_elimination model.(mabstract) elimination))) nil_elimination))) (tlocation type)) (tsubst (compose (apply_selection substitution) (apply_elimination (pair_elimination model.(mabstract) elimination))) type).
Proof.
  intros.
  eapply msubstv; eassumption.
Qed.



(* Part 11.2: The Graphical Core of an Expression *)

(* For an expression with given free variables, its corresponding graphical core has an additional free variable representing the expression's result type. *)
Definition EGraphicalCore (Input: Sort): Type
:= GraphicalCore (cons Unit Input).



(* The graphical core of a program variable is simply a constraint indicating that the type of that program variable must be a subtype of the result of the expression. *)
Definition EGCinput {Input: Sort} (input: SumSort Input): EGraphicalCore Input :=
{| GCAbstract := Empty;
   GCListener := Empty;
   GCNode := Empty;
   gcninterface := emptye;
   gcnargument := emptyde;
   GCConstraint := unit;
   gcclower _ := sortr (sortr (sortr (sortr input)));
   gccupper _ := sortr (sortr (sortr (sortr (sortl tt))));
   GCLKeyedS := emptye;
   gclaction := emptyde;
|}.
#[local] Instance EGCinput_Finite {Input: Sort} (input: SumSort Input): FiniteGraphicalCore (EGCinput input).
Proof.
  constructor; cbn; try apply _; intros [ ].
Qed.


(* The following define the graphical core of invocation expression. *)
Inductive EGCinvokeAbstract {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input}: Type
:= egciareceiver
 | egciaargument (parameter: scheme.(MInput) method)
 | egciareceiver_nested (abstract: receiver.(GCAbstract))
 | egciaargument_nested (parameter: scheme.(MInput) method) (abstract: (arguments parameter).(GCAbstract)).
Arguments EGCinvokeAbstract {_} _ _ _.
#[local] Instance EGCinvokeAbstract_SubFinite {Input: Sort} (receiver: EGraphicalCore Input) {receiver_Finite: FiniteGraphicalCore receiver} (method: scheme.(Method)) {MInput_Finite: Finite (scheme.(MInput) method)} (arguments: scheme.(MInput) method -> EGraphicalCore Input) {arguments_Finite: forall parameter: scheme.(MInput) method, FiniteGraphicalCore (arguments parameter)}: SubFinite (EGCinvokeAbstract receiver method arguments).
Proof.
  apply (inj_SubFinite (fun abstract => match abstract with
                                        | egciareceiver => None
                                        | egciaargument parameter => Some (inl parameter)
                                        | egciareceiver_nested abstract => Some (inr (inl abstract))
                                        | egciaargument_nested parameter abstract => Some (inr (inr (existT _ parameter abstract)))
                                        end)).
  intros abstract abstract' e.
  destruct abstract; destruct abstract'; inversion_hset e; reflexivity.
Qed.
Inductive EGCinvokeNode {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input}: Type
:= egcinreceiver_nested (node: receiver.(GCNode))
 | egcinargument_nested (parameter: scheme.(MInput) method) (node: (arguments parameter).(GCNode)).
Arguments EGCinvokeNode {_} _ _ _.
#[local] Instance EGCinvokeNode_SubFinite {Input: Sort} (receiver: EGraphicalCore Input) {receiver_Finite: FiniteGraphicalCore receiver} (method: scheme.(Method)) {MInput_Finite: Finite (scheme.(MInput) method)} (arguments: scheme.(MInput) method -> EGraphicalCore Input) {arguments_Finite: forall parameter: scheme.(MInput) method, FiniteGraphicalCore (arguments parameter)}: SubFinite (EGCinvokeNode receiver method arguments).
Proof.
  apply (inj_SubFinite (fun node => match node with
                                    | egcinreceiver_nested node => inl node
                                    | egcinargument_nested parameter node => inr (existT _ parameter node)
                                    end)).
  intros node node' e.
  destruct node; destruct node'; inversion_hset e; reflexivity.
Qed.
Definition egci_reciever {Input: Sort} (receiver: EGraphicalCore Input) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input): SortMorphism (cons receiver.(GCAbstract) (cons Unit Input)) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input))
:= pair_morphism (select_head egciareceiver_nested) (pair_morphism (select_head (fun _ => egciareceiver)) (extend_morphism _ (extend_morphism _ id_morphism))).
Definition egci_reciever_node {Input: Sort} (receiver: EGraphicalCore Input) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input): SortMorphism (cons Unit (cons receiver.(GCNode) (cons receiver.(GCAbstract) (cons Unit Input)))) (cons Unit (cons (EGCinvokeNode receiver method arguments) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input))))
:= consid_morphism Unit (cons_morphism egcinreceiver_nested (egci_reciever receiver method arguments)).
Definition egci_argument {Input: Sort} (receiver: EGraphicalCore Input) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input) (parameter: scheme.(MInput) method): SortMorphism (cons (arguments parameter).(GCAbstract) (cons Unit Input)) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input))
:= pair_morphism (select_head (egciaargument_nested parameter)) (pair_morphism (select_head (fun _ => egciaargument parameter)) (extend_morphism _ (extend_morphism _ id_morphism))).
Definition egci_argument_node {Input: Sort} (receiver: EGraphicalCore Input) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input) (parameter: scheme.(MInput) method): SortMorphism (cons Unit (cons (arguments parameter).(GCNode) (cons (arguments parameter).(GCAbstract) (cons Unit Input)))) (cons Unit (cons (EGCinvokeNode receiver method arguments) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input))))
:= consid_morphism Unit (cons_morphism (egcinargument_nested parameter) (egci_argument receiver method arguments parameter)).
Definition EGCinvokeninterface {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input} (node: EGCinvokeNode receiver method arguments): scheme.(Interface)
:= match node with
   | egcinreceiver_nested node => receiver.(gcninterface) node
   | egcinargument_nested parameter node => (arguments parameter).(gcninterface) node
   end.
Definition EGCinvokenargument {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input} (node: EGCinvokeNode receiver method arguments): scheme.(IParameter) (EGCinvokeninterface node) -> SumSort (cons Unit (cons (EGCinvokeNode receiver method arguments) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input))))
:= match node as node return scheme.(IParameter) (EGCinvokeninterface node) -> SumSort (cons Unit (cons (EGCinvokeNode receiver method arguments) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input)))) with
   | egcinreceiver_nested node => fun parameter' => apply_morphism (egci_reciever_node receiver method arguments) (receiver.(gcnargument) node parameter')
   | egcinargument_nested parameter node => fun parameter' => apply_morphism (egci_argument_node receiver method arguments parameter) ((arguments parameter).(gcnargument) node parameter')
   end.
Inductive EGCinvokeListener {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input}: Type
:= egcilreceiver
 | egcilreceiver_nested (listener: receiver.(GCListener))
 | egcilargument_nested (parameter: scheme.(MInput) method) (listener: (arguments parameter).(GCListener)).
Arguments EGCinvokeListener {_} _ _ _.
#[local] Instance EGCinvokeListener_SubFinite {Input: Sort} (receiver: EGraphicalCore Input) {receiver_Finite: FiniteGraphicalCore receiver} (method: scheme.(Method)) {MInput_Finite: Finite (scheme.(MInput) method)} (arguments: scheme.(MInput) method -> EGraphicalCore Input) {arguments_Finite: forall parameter: scheme.(MInput) method, FiniteGraphicalCore (arguments parameter)}: SubFinite (EGCinvokeListener receiver method arguments).
Proof.
  apply (inj_SubFinite (fun listener => match listener with
                                        | egcilreceiver => None
                                        | egcilreceiver_nested listener => Some (inl listener)
                                        | egcilargument_nested parameter listener => Some (inr (existT _ parameter listener))
                                        end)).
  intros listener listener' e.
  destruct listener; destruct listener'; inversion_hset e; reflexivity.
Qed.
Inductive EGCinvokeConstraint {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input}: Type
:= egcicreceiver
 | egcicreceiver_nested (constraint: receiver.(GCConstraint))
 | egcicargument_nested (parameter: scheme.(MInput) method) (constraint: (arguments parameter).(GCConstraint)).
Arguments EGCinvokeConstraint {_} _ _ _.
#[local] Instance EGCinvokeConstraint_Finite {Input: Sort} (receiver: EGraphicalCore Input) {receiver_Finite: FiniteGraphicalCore receiver} (method: scheme.(Method)) {MInput_Finite: Finite (scheme.(MInput) method)} (arguments: scheme.(MInput) method -> EGraphicalCore Input) {arguments_Finite: forall parameter: scheme.(MInput) method, FiniteGraphicalCore (arguments parameter)}: Finite (EGCinvokeConstraint receiver method arguments).
Proof.
  apply (bij_Finite (fun constraint => match constraint with
                                       | egcicreceiver => None
                                       | egcicreceiver_nested constraint => Some (inl constraint)
                                       | egcicargument_nested parameter constraint => Some (inr (existT _ parameter constraint))
                                       end)
                    (fun constraint => match constraint with
                                       | None => egcicreceiver
                                       | Some (inl constraint) => egcicreceiver_nested constraint
                                       | Some (inr (existT _ parameter constraint)) => egcicargument_nested parameter constraint
                                       end)).
  + intros constraint constraint' e.
    destruct constraint; destruct constraint'; inversion_hset e; reflexivity.
  + intros [ [ constraint | [ parameter constraint ] ] | ]; reflexivity.
Qed.
Definition EGCinvokeclower {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input} (constraint: EGCinvokeConstraint receiver method arguments): SumSort (cons Unit (cons (EGCinvokeNode receiver method arguments) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input))))
:= match constraint with
   | egcicreceiver => sortr (sortr (sortl egciareceiver))
   | egcicreceiver_nested constraint => apply_morphism (egci_reciever_node receiver method arguments) (receiver.(gcclower) constraint)
   | egcicargument_nested parameter constraint => apply_morphism (egci_argument_node receiver method arguments parameter) ((arguments parameter).(gcclower) constraint)
   end.
Definition EGCinvokecupper {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input} (constraint: EGCinvokeConstraint receiver method arguments): SumSort (cons (EGCinvokeListener receiver method arguments) (cons Unit (cons (EGCinvokeNode receiver method arguments) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input)))))
:= match constraint with
   | egcicreceiver => sortl egcilreceiver
   | egcicreceiver_nested constraint => apply_morphism (cons_morphism egcilreceiver_nested (egci_reciever_node receiver method arguments)) (receiver.(gccupper) constraint)
   | egcicargument_nested parameter constraint => apply_morphism (cons_morphism (egcilargument_nested parameter) (egci_argument_node receiver method arguments parameter)) ((arguments parameter).(gccupper) constraint)
   end.
Definition EGCinvokeKeyedS {Input: Sort} (receiver: EGraphicalCore Input) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input) (listener: EGCinvokeListener receiver method arguments): scheme.(Interface) -> SProp
:= match listener with
   | egcilreceiver => fun interface => SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method
   | egcilreceiver_nested listener => receiver.(GCLKeyedS) listener
   | egcilargument_nested parameter listener => (arguments parameter).(GCLKeyedS) listener
   end.
#[local] Instance EGCinvokeKeyedS_DecidableS {Input: Sort} (receiver: EGraphicalCore Input) {receiver_Finite: FiniteGraphicalCore receiver} (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input) {arguments_Finite: forall parameter: scheme.(MInput) method, FiniteGraphicalCore (arguments parameter)} (listener: EGCinvokeListener receiver method arguments) (interface: scheme.(Interface)): DecidableS (EGCinvokeKeyedS receiver method arguments listener interface).
Proof.
  destruct listener as [ | listener | parameter listener ]; simpl; apply _.
Qed.
Inductive EGCinvokeActionNode {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input} {interface: scheme.(Interface)} {keyed: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method}: Type
:= egcianinput (parameter: scheme.(MInput) method) (location: Location (((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method keyed).(umsinput) parameter))
 | egcianresult (location: Location ((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method keyed).(umsresult)).
Arguments EGCinvokeActionNode {_} _ _ _ _ _.
#[local] Instance EGCinvokeActionNode_SubFinite {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {Input: Sort} (receiver: EGraphicalCore Input) {receiver_Finite: FiniteGraphicalCore receiver} (method: scheme.(Method)) {MInput_Finite: Finite (scheme.(MInput) method)} (arguments: scheme.(MInput) method -> EGraphicalCore Input) (interface: scheme.(Interface)) (keyed: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method): SubFinite (EGCinvokeActionNode receiver method arguments interface keyed).
Proof.
  apply (inj_SubFinite (fun node => match node with
                                    | egcianinput parameter location => inl (existT _ parameter location)
                                    | egcianresult location => inr location
                                    end)).
  intros node node' e.
  destruct node; destruct node'; inversion_hset e; reflexivity.
Qed.
Definition EGCinvokeActionninterface {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input} {interface: scheme.(Interface)} {keyed: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method} (node: EGCinvokeActionNode receiver method arguments interface keyed): scheme.(Interface)
:= match node with
   | egcianinput parameter location => linterface location
   | egcianresult location => linterface location
   end.
Definition EGCinvokeActionnargument {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input} {interface: scheme.(Interface)} {keyed: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method} (node: EGCinvokeActionNode receiver method arguments interface keyed): scheme.(IParameter) (EGCinvokeActionninterface node) -> SumSort (cons Unit (cons (EGCinvokeActionNode receiver method arguments interface keyed) (cons Empty (cons (scheme.(IParameter) interface) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input))))))
:= match node as node return scheme.(IParameter) (EGCinvokeActionninterface node) -> SumSort (cons Unit (cons (EGCinvokeActionNode receiver method arguments interface keyed) (cons Empty (cons (scheme.(IParameter) interface) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input)))))) with
   | egcianinput parameter location => fun parameter' => apply_morphism (consid_morphism Unit
                                                                        (cons_morphism (egcianinput parameter)
                                                                        (extend_morphism Empty
                                                                        (consid_morphism (scheme.(IParameter) interface)
                                                                         nil_morphism))))
                                                                        (largument location parameter')
   | egcianresult location => fun parameter' => apply_morphism (consid_morphism Unit
                                                               (cons_morphism egcianresult
                                                               (extend_morphism Empty
                                                               (consid_morphism (scheme.(IParameter) interface)
                                                                nil_morphism))))
                                                               (largument location parameter')
   end.
Inductive EGCinvokeActionConstraint {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input} {interface: scheme.(Interface)} {keyed: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method}: Type
:= egciacargument (parameter: scheme.(MInput) method)
 | egciacresult.
Arguments EGCinvokeActionConstraint {_} _ _ _ _ _.
#[local] Instance EGCinvokeActionConstraint_Finite {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {Input: Sort} (receiver: EGraphicalCore Input) {receiver_Finite: FiniteGraphicalCore receiver} (method: scheme.(Method)) {MInput_Finite: Finite (scheme.(MInput) method)} (arguments: scheme.(MInput) method -> EGraphicalCore Input) (interface: scheme.(Interface)) (keyed: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method): Finite (EGCinvokeActionConstraint receiver method arguments interface keyed).
Proof.
  apply (bij_Finite (fun constraint => match constraint with
                                       | egciacargument parameter => Some parameter
                                       | egciacresult => None
                                       end)
                    (fun constraint => match constraint with
                                       | Some parameter => egciacargument parameter
                                       | None => egciacresult
                                       end)).
  + intros constraint constraint' e.
    destruct constraint; destruct constraint'; inversion_hset e; reflexivity.
  + intros [ constraint | ]; reflexivity.
Qed.
Definition EGCinvokeActionclower {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input} {interface: scheme.(Interface)} {keyed: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method} (constraint: EGCinvokeActionConstraint receiver method arguments interface keyed): SumSort (cons Unit (cons (EGCinvokeActionNode receiver method arguments interface keyed) (cons Empty (cons (scheme.(IParameter) interface) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input))))))
:= match constraint with
   | egciacargument parameter => sortr (sortr (sortr (sortr (sortl (egciaargument parameter)))))
   | egciacresult => apply_morphism (consid_morphism Unit
                                    (cons_morphism egcianresult
                                    (extend_morphism Empty
                                    (consid_morphism (scheme.(IParameter) interface)
                                     nil_morphism))))
                                    (tlocation ((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method keyed).(umsresult))
   end.
Definition EGCinvokeActioncupper {Input: Sort} {receiver: EGraphicalCore Input} {method: scheme.(Method)} {arguments: scheme.(MInput) method -> EGraphicalCore Input} {interface: scheme.(Interface)} {keyed: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method} (constraint: EGCinvokeActionConstraint receiver method arguments interface keyed): SumSort (cons Empty (cons Unit (cons (EGCinvokeActionNode receiver method arguments interface keyed) (cons Empty (cons (scheme.(IParameter) interface) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input)))))))
:= sortr (match constraint with
         | egciacargument parameter => apply_morphism (consid_morphism Unit
                                                      (cons_morphism (egcianinput parameter)
                                                      (extend_morphism Empty
                                                      (consid_morphism (scheme.(IParameter) interface)
                                                       nil_morphism))))
                                                      (tlocation (((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method keyed).(umsinput) parameter))
         | egciacresult => sortr (sortr (sortr (sortr (sortr (sortl tt)))))
         end).
Definition EGCinvokeAction {Input: Sort} (receiver: EGraphicalCore Input) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input) (listener: EGCinvokeListener receiver method arguments): forall interface: scheme.(Interface), EGCinvokeKeyedS receiver method arguments listener interface -> GraphicalCore (cons (scheme.(IParameter) interface) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input)))
:= match listener as listener return forall interface: scheme.(Interface), EGCinvokeKeyedS receiver method arguments listener interface -> GraphicalCore (cons (scheme.(IParameter) interface) (cons (EGCinvokeAbstract receiver method arguments) (cons Unit Input))) with
   | egcilreceiver => fun interface keyed => {| GCAbstract := Empty;
                                                GCListener := Empty;
                                                GCNode := EGCinvokeActionNode receiver method arguments interface keyed;
                                                gcninterface := EGCinvokeActionninterface;
                                                gcnargument := EGCinvokeActionnargument;
                                                GCConstraint := EGCinvokeActionConstraint receiver method arguments interface keyed;
                                                gcclower := EGCinvokeActionclower;
                                                gccupper := EGCinvokeActioncupper;
                                                GCLKeyedS := emptye;
                                                gclaction := emptyde;
                                              |}
   | egcilreceiver_nested listener => fun interface keyed => gcmap (consid_morphism (scheme.(IParameter) interface) (egci_reciever receiver method arguments)) (receiver.(gclaction) listener interface keyed)
   | egcilargument_nested parameter listener => fun interface keyed => gcmap (consid_morphism (scheme.(IParameter) interface) (egci_argument receiver method arguments parameter)) ((arguments parameter).(gclaction) listener interface keyed)
   end.
#[local] Instance EGCinvokeAction_Finite {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {Input: Sort} (receiver: EGraphicalCore Input) {receiver_Finite: FiniteGraphicalCore receiver} (method: scheme.(Method)) {MInput_Finite: Finite (scheme.(MInput) method)} (arguments: scheme.(MInput) method -> EGraphicalCore Input) {arguments_Finite: forall parameter: scheme.(MInput) method, FiniteGraphicalCore (arguments parameter)} (listener: EGCinvokeListener receiver method arguments) (interface: scheme.(Interface)) (keyed: EGCinvokeKeyedS receiver method arguments listener interface): FiniteGraphicalCore (EGCinvokeAction receiver method arguments listener interface keyed).
Proof.
  destruct listener as [ | listener | parameter listener ]; simpl; try apply _.
  constructor; try apply _; cbn; intros [ ].
Qed.
Definition EGCinvoke {Input: Sort} (receiver: EGraphicalCore Input) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input): EGraphicalCore Input :=
{| GCAbstract := EGCinvokeAbstract receiver method arguments;
   GCListener := EGCinvokeListener receiver method arguments;
   GCNode := EGCinvokeNode receiver method arguments;
   gcninterface := EGCinvokeninterface;
   gcnargument := EGCinvokenargument;
   GCConstraint := EGCinvokeConstraint receiver method arguments;
   gcclower := EGCinvokeclower;
   gccupper := EGCinvokecupper;
   GCLKeyedS := EGCinvokeKeyedS receiver method arguments;
   gclaction := EGCinvokeAction receiver method arguments;
|}.
#[local] Instance EGCinvoke_Finite {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {Input: Sort} (receiver: EGraphicalCore Input) {receiver_Finite: FiniteGraphicalCore receiver} (method: scheme.(Method)) {MInput_Finite: Finite (scheme.(MInput) method)} (arguments: scheme.(MInput) method -> EGraphicalCore Input) {arguments_Finite: forall parameter: scheme.(MInput) method, FiniteGraphicalCore (arguments parameter)}: FiniteGraphicalCore (EGCinvoke receiver method arguments).
Proof.
  constructor; cbn; apply _.
Qed.



(* The following define the graphical core of an object expression. *)
Inductive EGCobjectAbstract {Input: Sort} {interface: scheme.(Interface)} {methods: SCSet scheme.(Method)} {bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)}: Type
:= egcoaparameter (parameter: scheme.(IParameter) interface)
 | egcoainput (method: scheme.(Method)) (contains: SCSetContains methods method) (parameter: scheme.(MInput) method)
 | egcoaresult (method: scheme.(Method)) (contains: SCSetContains methods method)
 | egcoabody_nested (method: scheme.(Method)) (contains: SCSetContains methods method) (abstract: (bodies method contains).(GCAbstract)).
Arguments EGCobjectAbstract {_} _ _ _.
#[local] Instance EGCobjectAbstract_SubFinite {IParameter_SubFinite: forall interface: scheme.(Interface), SubFinite (scheme.(IParameter) interface)} {MInput_SubFinite: forall method: scheme.(Method), SubFinite (scheme.(MInput) method)} {Input: Sort} (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)) {bodies_Finite: forall method: scheme.(Method), forall contains: SCSetContains methods method, FiniteGraphicalCore (bodies method contains)}: SubFinite (EGCobjectAbstract interface methods bodies).
Proof.
  apply (inj_SubFinite (fun abstract => match abstract with
                                              | egcoaparameter parameter => inl parameter
                                              | egcoainput method contains parameter => inr (inl (existSdT method contains parameter))
                                              | egcoaresult method contains => inr (inr (inl (existSdT method contains tt)))
                                              | egcoabody_nested method contains abstract => inr (inr (inr (existSdT method contains abstract)))
                                              end)).
  intros abstract abstract' e.
  destruct abstract; destruct abstract'; try discriminate e.
  + inversion_hset e; reflexivity.
  + inversion_hset e; reflexivity.
  + inversion_hset e; reflexivity.
  + apply inr_inj in e.
    apply inr_inj in e.
    apply inr_inj in e.
    pose proof e as e1.
    apply proj1_sigSdT_eq in e1.
    cbn in e1.
    destruct e1.
    merge contains contains0.
    apply hsetS_inj_proj3_sigSdT in e.
    destruct e.
    reflexivity.
Qed.
Inductive EGCobjectNode {Input: Sort} {interface: scheme.(Interface)} {methods: SCSet scheme.(Method)} {bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)}: Type
:= egconobject
 | egconinput (method: scheme.(Method)) (contains: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method) (parameter: scheme.(MInput) method) (location: Location (((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method contains).(umsinput) parameter))
 | egconresult (method: scheme.(Method)) (contains: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method) (location: Location (((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method contains).(umsresult)))
 | egconbody_nested (method: scheme.(Method)) (contains: SCSetContains methods method) (node: (bodies method contains).(GCNode)).
Arguments EGCobjectNode {_} _ _ _.
#[local] Instance EGCobjectNode_SubFinite {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {MInput_Finite: forall method: scheme.(Method), Finite (scheme.(MInput) method)} {Input: Sort} (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)) {bodies_Finite: forall method: scheme.(Method), forall contains: SCSetContains methods method, FiniteGraphicalCore (bodies method contains)}: SubFinite (EGCobjectNode interface methods bodies).
Proof.
  apply (inj_SubFinite (fun node => match node with
                                    | egconobject => None
                                    | egconinput method contains parameter location => Some (inl (existSdT method contains (existT _ parameter location)))
                                    | egconresult method contains location => Some (inr (inl (existSdT method contains location)))
                                    | egconbody_nested method contains node => Some (inr (inr (existSdT method contains node)))
                                    end)).
  intros node node' e.
  destruct node; destruct node'; try discriminate e.
  + inversion_hset e; reflexivity.
  + apply Some_inj in e.
    apply inl_inj in e.
    pose proof e as e1.
    apply proj1_sigSdT_eq in e1.
    cbn in e1.
    destruct e1.
    merge contains contains0.
    apply hsetS_inj_proj3_sigSdT in e.
    inversion_hset e.
    reflexivity.
  + apply Some_inj in e.
    apply inr_inj in e.
    apply inl_inj in e.
    pose proof e as e1.
    apply proj1_sigSdT_eq in e1.
    cbn in e1.
    destruct e1.
    merge contains contains0.
    apply hsetS_inj_proj3_sigSdT in e.
    destruct e.
    reflexivity.
  + apply Some_inj in e.
    apply inr_inj in e.
    apply inr_inj in e.
    pose proof e as e1.
    apply proj1_sigSdT_eq in e1.
    cbn in e1.
    destruct e1.
    merge contains contains0.
    apply hsetS_inj_proj3_sigSdT in e.
    destruct e.
    reflexivity.
Qed.
Definition egco_body {Input: Sort} (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)) (method: scheme.(Method)) (contains: SCSetContains methods method): SortMorphism (cons (bodies method contains).(GCAbstract) (cons Unit (cons (scheme.(MInput) method) Input))) (cons (EGCobjectAbstract interface methods bodies) (cons Unit Input))
:= pair_morphism (select_head (egcoabody_nested method contains)) (pair_morphism (select_head (fun _ => egcoaresult method contains)) (pair_morphism (select_head (egcoainput method contains)) (extend_morphism _ (extend_morphism _ id_morphism)))).
Definition egco_body_node {Input: Sort} (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)) (method: scheme.(Method)) (contains: SCSetContains methods method): SortMorphism (cons Unit (cons (bodies method contains).(GCNode) (cons (bodies method contains).(GCAbstract) (cons Unit (cons (scheme.(MInput) method) Input))))) (cons Unit (cons (EGCobjectNode interface methods bodies) (cons (EGCobjectAbstract interface methods bodies) (cons Unit Input))))
:= consid_morphism Unit (cons_morphism (egconbody_nested method contains) (egco_body interface methods bodies method contains)).
Definition EGCobjectninterface {Input: Sort} {interface: scheme.(Interface)} {methods: SCSet scheme.(Method)} {bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)} (node: EGCobjectNode interface methods bodies): scheme.(Interface)
:= match node with
   | egconobject => interface
   | egconinput method contains parameter location => linterface location
   | egconresult method contains location => linterface location
   | egconbody_nested method contains node => (bodies method contains).(gcninterface) node
   end.
Definition EGCobjectnargument {Input: Sort} {interface: scheme.(Interface)} {methods: SCSet scheme.(Method)} {bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)} (node: EGCobjectNode interface methods bodies): scheme.(IParameter) (EGCobjectninterface node) -> SumSort (cons Unit (cons (EGCobjectNode interface methods bodies) (cons (EGCobjectAbstract interface methods bodies) (cons Unit Input))))
:= match node as node return scheme.(IParameter) (EGCobjectninterface node) -> SumSort (cons Unit (cons (EGCobjectNode interface methods bodies) (cons (EGCobjectAbstract interface methods bodies) (cons Unit Input)))) with
   | egconobject => fun parameter' => sortr (sortr (sortl (egcoaparameter parameter')))
   | egconinput method contains parameter location => fun parameter' => apply_morphism (consid_morphism Unit
                                                                                       (cons_morphism (egconinput method contains parameter)
                                                                                       (cons_morphism egcoaparameter
                                                                                        nil_morphism)))
                                                                                       (largument location parameter')
   | egconresult method contains location => fun parameter' => apply_morphism (consid_morphism Unit
                                                                              (cons_morphism (egconresult method contains)
                                                                              (cons_morphism egcoaparameter
                                                                               nil_morphism)))
                                                                              (largument location parameter')
   | egconbody_nested method contains node => fun parameter' => apply_morphism (egco_body_node interface methods bodies method contains) ((bodies method contains).(gcnargument) node parameter')
   end.
Inductive EGCobjectListener {Input: Sort} {interface: scheme.(Interface)} {methods: SCSet scheme.(Method)} {bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)}: Type
:= egcolbody_nested (method: scheme.(Method)) (contains: SCSetContains methods method) (listener: (bodies method contains).(GCListener)).
Arguments EGCobjectListener {_} _ _ _.
#[local] Instance EGCobjectListener_SubFinite {Input: Sort} (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)) {bodies_Finite: forall method: scheme.(Method), forall contains: SCSetContains methods method, FiniteGraphicalCore (bodies method contains)}: SubFinite (EGCobjectListener interface methods bodies).
Proof.
  apply (inj_SubFinite (fun listener => match listener with
                                        | egcolbody_nested method contains listener => existSdT method contains listener
                                        end)).
  intros listener listener' e.
  destruct listener; destruct listener'.
  pose proof e as e1.
  apply proj1_sigSdT_eq in e1.
  cbn in e1.
  destruct e1.
  merge contains contains0.
  apply hsetS_inj_proj3_sigSdT in e.
  destruct e.
  reflexivity.
Qed.
Definition EGCobjectKeyedS {Input: Sort} {interface: scheme.(Interface)} {methods: SCSet scheme.(Method)} {bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)} (listener: EGCobjectListener interface methods bodies): scheme.(Interface) -> SProp
:= match listener with
   | egcolbody_nested method contains listener => (bodies method contains).(GCLKeyedS) listener
   end.
#[local] Instance EGCobjectKeyedS_DecidableS {Input: Sort} (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)) {bodies_Finite: forall method: scheme.(Method), forall contains: SCSetContains methods method, FiniteGraphicalCore (bodies method contains)} (listener: EGCobjectListener interface methods bodies) (interface': scheme.(Interface)): DecidableS (EGCobjectKeyedS listener interface').
Proof.
  destruct listener as [ method contains listener ].
  simpl.
  apply _.
Qed.
Definition EGCobjectAction {Input: Sort} {interface: scheme.(Interface)} {methods: SCSet scheme.(Method)} {bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)} (listener: EGCobjectListener interface methods bodies): forall interface': scheme.(Interface), EGCobjectKeyedS listener interface' -> GraphicalCore (cons (scheme.(IParameter) interface') (cons (EGCobjectAbstract interface methods bodies) (cons Unit Input)))
:= match listener as listener return forall interface': scheme.(Interface), EGCobjectKeyedS listener interface' -> GraphicalCore (cons (scheme.(IParameter) interface') (cons (EGCobjectAbstract interface methods bodies) (cons Unit Input))) with
   | egcolbody_nested method contains listener => fun interface' keyed => gcmap (consid_morphism (scheme.(IParameter) interface') (egco_body interface methods bodies method contains)) ((bodies method contains).(gclaction) listener interface' keyed)
   end.
#[local] Instance EGCobjectAction_Finite {Input: Sort} {interface: scheme.(Interface)} {methods: SCSet scheme.(Method)} {bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)} {bodies_Finite: forall method: scheme.(Method), forall contains: SCSetContains methods method, FiniteGraphicalCore (bodies method contains)} (listener: EGCobjectListener interface methods bodies) (interface': scheme.(Interface)) (keyed': EGCobjectKeyedS listener interface'): FiniteGraphicalCore (EGCobjectAction listener interface' keyed').
Proof.
  destruct listener as [ method contains listener ].
  simpl.
  apply _.
Qed.
Inductive EGCobjectConstraint {Input: Sort} {interface: scheme.(Interface)} {methods: SCSet scheme.(Method)} {bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)}: Type
:= egcocobject
 | egcocinput (method: scheme.(Method)) (contains: SCSetContains methods method) (contains': SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method) (parameter: scheme.(MInput) method)
 | egcocresult (method: scheme.(Method)) (contains: SCSetContains methods method) (contains': SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method)
 | egcocbody_nested (method: scheme.(Method)) (contains: SCSetContains methods method) (constraint: (bodies method contains).(GCConstraint)).
Arguments EGCobjectConstraint {_} _ _ _.
#[local] Instance EGCobjectConstraint_Finite {MInput_Finite: forall method: scheme.(Method), Finite (scheme.(MInput) method)} {Input: Sort} {interface: scheme.(Interface)} {methods: SCSet scheme.(Method)} {bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)} {bodies_Finite: forall method: scheme.(Method), forall contains: SCSetContains methods method, FiniteGraphicalCore (bodies method contains)}: Finite (EGCobjectConstraint interface methods bodies).
Proof.
  apply (bij_Finite (fun constraint => match constraint with
                                       | egcocobject => None
                                       | egcocinput method contains contains' parameter => Some (inl (existSdT method contains (pair (box contains') parameter)))
                                       | egcocresult method contains contains' => Some (inr (inl (existSdT method contains (box contains'))))
                                       | egcocbody_nested method contains constraint => Some (inr (inr (existSdT method contains constraint)))
                                       end)
                    (fun constraint => match constraint return EGCobjectConstraint interface methods bodies with
                                       | None => egcocobject
                                       | Some (inl (existSdT method contains (pair (box contains') parameter))) => egcocinput method contains contains' parameter
                                       | Some (inr (inl (existSdT method contains (box contains')))) => egcocresult method contains contains'
                                       | Some (inr (inr (existSdT method contains constraint))) => egcocbody_nested method contains constraint
                                       end)).
  + intros constraint constraint' e.
    destruct constraint; destruct constraint'; try discriminate e.
    - reflexivity.
    - apply Some_inj in e.
      apply inl_inj in e.
      pose proof e as e1.
      apply proj1_sigSdT_eq in e1.
      cbn in e1.
      destruct e1.
      merge contains contains0.
      apply hsetS_inj_proj3_sigSdT in e.
      inversion e.
      reflexivity.
    - apply Some_inj in e.
      apply inr_inj in e.
      apply inl_inj in e.
      pose proof e as e1.
      apply proj1_sigSdT_eq in e1.
      cbn in e1.
      destruct e1.
      merge contains contains0.
      apply hsetS_inj_proj3_sigSdT in e.
      destruct e.
      reflexivity.
    - apply Some_inj in e.
      apply inr_inj in e.
      apply inr_inj in e.
      pose proof e as e1.
      apply proj1_sigSdT_eq in e1.
      cbn in e1.
      destruct e1.
      merge contains contains0.
      apply hsetS_inj_proj3_sigSdT in e.
      destruct e.
      reflexivity.
  + intros [ [ [ method contains [ [ contains' ] parameter ] ] | [ [ method contains [ contains' ] ] | [ method contains constraint ] ] ] | ]; reflexivity.
Qed.
Definition EGCobjectclower {Input: Sort} {interface: scheme.(Interface)} {methods: SCSet scheme.(Method)} {bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)} (constraint: EGCobjectConstraint interface methods bodies): SumSort (cons Unit (cons (EGCobjectNode interface methods bodies) (cons (EGCobjectAbstract interface methods bodies) (cons Unit Input))))
:= match constraint with
   | egcocobject => sortr (sortl egconobject)
   | egcocinput method contains contains' parameter => apply_morphism (consid_morphism Unit
                                                                      (cons_morphism (egconinput method contains' parameter)
                                                                      (cons_morphism egcoaparameter
                                                                       nil_morphism)))
                                                                      (tlocation (((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method contains').(umsinput) parameter))
   | egcocresult method contains contains' => sortr (sortr (sortl (egcoaresult method contains)))
   | egcocbody_nested method contains constraint => apply_morphism (egco_body_node interface methods bodies method contains) ((bodies method contains).(gcclower) constraint)
   end.
Definition EGCobjectcupper {Input: Sort} {interface: scheme.(Interface)} {methods: SCSet scheme.(Method)} {bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)} (constraint: EGCobjectConstraint interface methods bodies): SumSort (cons (EGCobjectListener interface methods bodies) (cons Unit (cons (EGCobjectNode interface methods bodies) (cons (EGCobjectAbstract interface methods bodies) (cons Unit Input)))))
:= match constraint with
   | egcocobject => sortr (sortr (sortr (sortr (sortl tt))))
   | egcocinput method contains contains' parameter => sortr (sortr (sortr (sortl (egcoainput method contains parameter))))
   | egcocresult method contains contains' => sortr (apply_morphism (consid_morphism Unit
                                                                    (cons_morphism (egconresult method contains')
                                                                    (cons_morphism egcoaparameter
                                                                     nil_morphism)))
                                                                    (tlocation ((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method contains').(umsresult)))
   | egcocbody_nested method contains constraint => apply_morphism (cons_morphism (egcolbody_nested method contains) (egco_body_node interface methods bodies method contains)) ((bodies method contains).(gccupper) constraint)
   end.
Definition EGCobject {Input: Sort} (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)): EGraphicalCore Input :=
{| GCAbstract := EGCobjectAbstract interface methods bodies;
   GCListener := EGCobjectListener interface methods bodies;
   GCNode := EGCobjectNode interface methods bodies;
   gcninterface := EGCobjectninterface;
   gcnargument := EGCobjectnargument;
   GCConstraint := EGCobjectConstraint interface methods bodies;
   gcclower := EGCobjectclower;
   gccupper := EGCobjectcupper;
   GCLKeyedS := EGCobjectKeyedS;
   gclaction := EGCobjectAction;
|}.
#[local] Instance EGCobject_Finite {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {MInput_Finite: forall method: scheme.(Method), Finite (scheme.(MInput) method)} {Input: Sort} {interface: scheme.(Interface)} {methods: SCSet scheme.(Method)} {bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)} {bodies_Finite: forall method: scheme.(Method), forall contains: SCSetContains methods method, FiniteGraphicalCore (bodies method contains)}: FiniteGraphicalCore (EGCobject interface methods bodies).
Proof.
  constructor; cbn; try apply _.
Qed.



(* Using the above, egraphicalcore recursively constructs the graphical core of an expression. *)
Definition egraphicalcore: forall {Input: Sort} (expression: Expression Input), EGraphicalCore Input
:= fix egraphicalcore {Input: Sort} (expression: Expression Input): EGraphicalCore Input
:= match expression as expression return EGraphicalCore Input with
   | einput input => EGCinput input
   | einvoke receiver method arguments => EGCinvoke (egraphicalcore receiver) method (fun parameter => egraphicalcore (arguments parameter))
   | eobject interface methods bodies => EGCobject interface methods (fun method contains => egraphicalcore (bodies method contains))
   end.
#[local] Instance egraphicalcore_Finite {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {MInput_Finite: forall method: scheme.(Method), Finite (scheme.(MInput) method)} {Input: Sort} (expression: Expression Input): FiniteGraphicalCore (egraphicalcore expression).
Proof.
  induction expression; simpl; apply _.
Qed.



(* Part 11.3: Completeness of Extraction from an Expression
 * Here we prove the only-if direction of Lemma 9.1: that the expression type-checks within a type space only if that type space models its extracted graphical core.
 *)

Lemma egraphicalcore_complete
      {Interface_SSet: SSet scheme.(Interface)}
      {MInput_SSet: forall method: scheme.(Method), SSet (scheme.(MInput) method)}
      {MInput_Projective: forall method: scheme.(Method), Projective (scheme.(MInput) method)}
      {Input: Sort}
      (expression: Expression Input)
      (space: TypeSpace)
      (context: SortElimination space.(SpaceType) Input)
      (result: space.(SpaceType))
    : HierarchyV
   -> CheckExpression space context expression result
   -> existsTSS history: GCHistory (egraphicalcore expression),
      FinalGCHistory history
    & existsTS model: Model history space,
      ModelV model (pair_elimination (fun _ => result) context).
Proof.
  intros vhierarchy check.
  assert (existsTSS history: GCHistory (egraphicalcore expression), FinalGCHistory history & existsTS model: Model history space, forall result', space.(SubSpaceType) result result' -> ModelV model (pair_elimination (fun _ => result') context)) as [ history consistent [ model vmodel ] ]; [ | exists history; try assumption; exists model; apply vmodel; apply sstrefl ].
  induction check; simpl.
  + destruct IHcheck as [ history final [ model vmodel ] ].
    exists history; try assumption.
    exists model.
    intros result' subresult.
    apply vmodel.
    eapply space.(ssttrans); eassumption.
  + exists (Build_GCHistory _ (EGCinput input) emptye emptye emptydSe emptyde).
    - constructor; cbn; intros [ ].
    - exists (Build_Model _ (EGCinput input) _ space emptye emptye emptye emptyde emptyde).
      constructor; try (intros [ ]; fail).
      cbn.
      intros _.
      assumption.
  + clear check c0.
    rename c into checkmethod.
    rename H into IHargument.
    destruct IHcheck as [ receiver_history consistent_receiver_history [ reciever_model receiver_vmodel ] ].
    specialize (receiver_vmodel treceiver (space.(sstrefl) treceiver)).
    apply projectiveD2 in IHargument.
    destruct IHargument as [ argument_history consistent_argument_history IHargument ].
    apply projectiveD in IHargument.
    destruct IHargument as [ argument_model argument_vmodel ].
    specialize (fun parameter => argument_vmodel parameter (signature.(smsinput) parameter) (space.(sstrefl) (signature.(smsinput) parameter))).
    assert (existsTSS configuration: option scheme.(Interface), match configuration with None => space.(UnReachable) treceiver | Some _ => TrueS end & existsTSS arguments: forall interface, match configuration with None => FalseS | Some interface' => eqS interface interface' end -> scheme.(IParameter) interface -> space.(SpaceType), forall interface e, space.(SubSpaceType) treceiver (space.(stinterface) interface (arguments interface e)) & forall interface e, existsSS contains: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method, eqS (mssubst (arguments interface e) ((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method contains)) signature) as [ configuration ur [ arguments sub contains ] ] by (destruct checkmethod; [ exists None; try assumption; exists (fun interface => falseSe); intros _ [ ] | exists (Some interface); try constructor; exists (fun interface' e parameter => arguments (convert e scheme.(IParameter) parameter)); intros ? e; destruct (eqS_eq e); rewrite convert_id; clear e; [ apply sstrefl | exists contains; reflexivity ] ]); clear checkmethod.
    pose (fun listener => match listener with
          | egcilreceiver => fun interface => match configuration with None => FalseS | Some interface' => eqS interface interface' end
          | egcilreceiver_nested listener => receiver_history.(GCHKeyedS) listener
          | egcilargument_nested parameter listener => (argument_history parameter).(GCHKeyedS) listener
          end) as invokeGCHKeyedS.
    pose (fun listener => match listener with
          | egcilreceiver => match configuration with None => TrueS | Some _ => FalseS end
          | egcilreceiver_nested listener => receiver_history.(GCHUnResolvedS) listener
          | egcilargument_nested parameter listener => (argument_history parameter).(GCHUnResolvedS) listener
          end) as invokeGCHUnResolvedS.
    assert (forall listener interface, invokeGCHKeyedS listener interface -> EGCinvokeKeyedS _ _ _ listener interface) as invokegchkeyed.
    - cbn.
      intros listener interface.
      destruct listener as [ | listener | parameter listener ]; simpl.
      * destruct configuration as [ interface' | ].
        ** intro e.
           specialize (contains _ e).
           destruct contains as [ ? _ ].
           assumption.
        ** intros [ ].
        * apply receiver_history.(gchkeyed).
        * apply (argument_history parameter).(gchkeyed).
      - pose (fun listener => match listener as listener return forall interface hkeyed, GCHistory (EGCinvokeAction _ _ _ listener interface (invokegchkeyed listener interface hkeyed)) with
                              | egcilreceiver => fun interface hkeyed => Build_GCHistory _ (EGCinvokeAction _ _ _ egcilreceiver interface _) emptye emptye emptydSe emptyde
                              | egcilreceiver_nested listener => fun interface hkeyed => gcmap_history _ (receiver_history.(gchaction) listener interface hkeyed)
                              | egcilargument_nested parameter listener => fun interface hkeyed => gcmap_history _ ((argument_history parameter).(gchaction) listener interface hkeyed)
                              end) as invokegchaction.
        pose (Build_GCHistory _ (EGCinvoke (egraphicalcore ereceiver) method (compose einputs egraphicalcore))
                              invokeGCHKeyedS
                              invokeGCHUnResolvedS
                              invokegchkeyed
                              invokegchaction) as invokehistory.
        exists invokehistory.
        * constructor; cbn.
          ** intros [ | listener | parameter listener ] interface interface'; simpl.
             *** intros hkeyed hkeyed'; destruct configuration; destruct hkeyed; destruct hkeyed'; reflexivity.
             *** apply consistent_receiver_history.(fgchunique).
             *** apply (consistent_argument_history parameter).(fgchunique).
          ** intros [ | listener | parameter listener ]; simpl.
             *** destruct configuration; [ intros [ ] | intros _ _ [ ] ].
             *** apply consistent_receiver_history.(fgchunresolved).
             *** apply (consistent_argument_history parameter).(fgchunresolved).
          ** intros [ | listener | parameter listener ]; simpl.
             *** destruct configuration as [ interface | ]; [ right; eexists; constructor; reflexivity | left; constructor; constructor ].
             *** apply consistent_receiver_history.(fgchresolved).
             *** apply (consistent_argument_history parameter).(fgchresolved).
          ** intros [ | listener | parameter listener ]; simpl.
             *** intros.
                 constructor; intros [ ].
             *** intros.
                 apply final_gcmap_history.
                 apply consistent_receiver_history.(fgchaction).
             *** intros.
                 apply final_gcmap_history.
                 apply (consistent_argument_history parameter).(fgchaction).
        * exists (Build_Model _ _ invokehistory space
                              (fun abstract => match abstract with
                                               | egciareceiver => treceiver
                                               | egciaargument parameter => signature.(smsinput) parameter
                                               | egciareceiver_nested abstract => reciever_model.(mabstract) abstract
                                               | egciaargument_nested parameter abstract => (argument_model parameter).(mabstract) abstract
                                               end)
                              (fun listener => match listener with
                                               | egcilreceiver => treceiver
                                               | egcilreceiver_nested listener => reciever_model.(mlistener) listener
                                               | egcilargument_nested parameter listener => (argument_model parameter).(mlistener) listener
                                               end)
                              (fun node => match node with
                                           | egcinreceiver_nested node => reciever_model.(mnode) node
                                           | egcinargument_nested parameter node => (argument_model parameter).(mnode) node
                                           end)
                              (fun listener => match listener as listener return forall interface (hkeyed: invokeGCHKeyedS listener interface), scheme.(IParameter) interface -> space.(SpaceType) with
                                               | egcilreceiver => fun interface hkeyed => arguments interface hkeyed
                                               | egcilreceiver_nested listener => fun interface hkeyed => reciever_model.(mlargument) listener interface hkeyed
                                               | egcilargument_nested parameter listener => fun interface hkeyed => (argument_model parameter).(mlargument) listener interface hkeyed
                                               end)
                              (fun listener => match listener as listener return forall interface hkeyed, Model (invokegchaction listener interface hkeyed) space with
                                               | egcilreceiver => fun interface hkeyed => Build_Model _ _ (invokegchaction egcilreceiver interface hkeyed) space
                                                                                                      emptye
                                                                                                      emptye
                                                                                                      (fun node => match node with
                                                                                                                   | egcianinput parameter location => space.(stinterface) (linterface location) (fun parameter => tsubst (arguments interface hkeyed) (ltargument location parameter))
                                                                                                                   | egcianresult location => space.(stinterface) (linterface location) (fun parameter => tsubst (arguments interface hkeyed) (ltargument location parameter))
                                                                                                                   end)
                                                                                                      emptyde
                                                                                                      emptyde
                                               | egcilreceiver_nested listener => fun interface hkeyed => gcmap_model _ (reciever_model.(mlaction) listener interface hkeyed)
                                               | egcilargument_nested parameter listener => fun interface hkeyed => gcmap_model _ ((argument_model parameter).(mlaction) listener interface hkeyed)
                                               end)).
          intros result subresult.
          constructor.
          ** intros [ | constraint | parameter constraint ]; unfold meliminatel; unfold meliminationl; unfold meliminate; unfold melimination; cbn.
             *** apply space.(sstrefl).
             *** rewrite <- apply_eliminate_morphism.
                 rewrite <- apply_eliminate_morphism.
                 rewrite eliminate_cons_pair_elimination.
                 unfold egci_reciever_node.
                 rewrite eliminate_consid_pair_elimination.
                 rewrite eliminate_cons_pair_elimination.
                 unfold egci_reciever.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_id_morphism.
                 unfold compose.
                 apply receiver_vmodel.(mconstraintv).
             *** rewrite <- apply_eliminate_morphism.
                 rewrite <- apply_eliminate_morphism.
                 rewrite eliminate_cons_pair_elimination.
                 unfold egci_argument_node.
                 rewrite eliminate_consid_pair_elimination.
                 rewrite eliminate_cons_pair_elimination.
                 unfold egci_argument.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_id_morphism.
                 unfold compose.
                 apply (argument_vmodel parameter).(mconstraintv).
          ** intros [ node | parameter node ]; unfold meliminatel; unfold meliminationl; unfold meliminate; unfold melimination; cbn.
             *** eapply space.(ssttrans); try apply receiver_vmodel.(mlowerv).
                 apply space.(sstvariance).
                 intro parameter.
                 rewrite <- apply_eliminate_morphism.
                 unfold egci_reciever_node.
                 rewrite eliminate_consid_pair_elimination.
                 rewrite eliminate_cons_pair_elimination.
                 unfold egci_reciever.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_id_morphism.
                 unfold compose.
                 apply signed_refl.
                 apply space.(sstrefl).
             *** eapply space.(ssttrans); try apply (argument_vmodel parameter).(mlowerv).
                 apply space.(sstvariance).
                 intro parameter'.
                 rewrite <- apply_eliminate_morphism.
                 unfold egci_argument_node.
                 rewrite eliminate_consid_pair_elimination.
                 rewrite eliminate_cons_pair_elimination.
                 unfold egci_argument.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_id_morphism.
                 unfold compose.
                 apply signed_refl.
                 apply space.(sstrefl).
          ** intros [ node | parameter node ]; unfold meliminatel; unfold meliminationl; unfold meliminate; unfold melimination; cbn.
             *** eapply space.(ssttrans); try apply receiver_vmodel.(mupperv).
                 apply space.(sstvariance).
                 intro parameter.
                 rewrite <- apply_eliminate_morphism.
                 unfold egci_reciever_node.
                 rewrite eliminate_consid_pair_elimination.
                 rewrite eliminate_cons_pair_elimination.
                 unfold egci_reciever.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_id_morphism.
                 unfold compose.
                 apply signed_refl.
                 apply space.(sstrefl).
             *** eapply space.(ssttrans); try apply (argument_vmodel parameter).(mupperv).
                 apply space.(sstvariance).
                 intro parameter'.
                 rewrite <- apply_eliminate_morphism.
                 unfold egci_argument_node.
                 rewrite eliminate_consid_pair_elimination.
                 rewrite eliminate_cons_pair_elimination.
                 unfold egci_argument.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_id_morphism.
                 unfold compose.
                 apply signed_refl.
                 apply space.(sstrefl).
          ** intros [ | listener | parameter listener ] interface hkeyed; cbn in *.
             *** apply sub.
             *** apply receiver_vmodel.(mlargumentv).
             *** apply (argument_vmodel parameter).(mlargumentv).
          ** intros [ | listener | parameter listener ] interface hkeyed; cbn in *.
             *** specialize (contains interface hkeyed).
                 destruct contains as [ contains esignature ].
                 merge contains (invokegchkeyed egcilreceiver interface hkeyed).
                 constructor; cbn.
                 **** intros [ parameter | ]; unfold meliminate; unfold melimination; cbn; destruct esignature; cbn in *.
                      ***** rewrite <- apply_eliminate_morphism.
                            rewrite eliminate_consid_pair_elimination.
                            rewrite eliminate_cons_pair_elimination.
                            rewrite eliminate_pair_morphism.
                            rewrite eliminate_extend_selection_pair_elimination.
                            rewrite eliminate_select_head_pair_elimination.
                            rewrite eliminate_nil_morphism.
                            unfold compose.
                            rewrite tsubst_tlocation.
                            apply space.(sstrefl).
                      ***** rewrite <- apply_eliminate_morphism.
                            rewrite eliminate_consid_pair_elimination.
                            rewrite eliminate_cons_pair_elimination.
                            rewrite eliminate_pair_morphism.
                            rewrite eliminate_extend_selection_pair_elimination.
                            rewrite eliminate_select_head_pair_elimination.
                            rewrite eliminate_nil_morphism.
                            unfold compose.
                            eapply space.(ssttrans); try apply subresult.
                            rewrite tsubst_tlocation.
                            apply space.(sstrefl).
                 **** unfold meliminate; unfold melimination; cbn.
                      intros [ parameter location | location ]; apply space.(sstvariance); intro parameter'; cbn.
                      ***** rewrite <- apply_eliminate_morphism.
                            rewrite eliminate_consid_pair_elimination.
                            rewrite eliminate_cons_pair_elimination.
                            rewrite eliminate_pair_morphism.
                            rewrite eliminate_extend_selection_pair_elimination.
                            rewrite eliminate_select_head_pair_elimination.
                            rewrite eliminate_nil_morphism.
                            unfold compose.
                            rewrite tsubst_ltargument.
                            apply signed_refl.
                            apply space.(sstrefl).
                      ***** rewrite <- apply_eliminate_morphism.
                            rewrite eliminate_consid_pair_elimination.
                            rewrite eliminate_cons_pair_elimination.
                            rewrite eliminate_pair_morphism.
                            rewrite eliminate_extend_selection_pair_elimination.
                            rewrite eliminate_select_head_pair_elimination.
                            rewrite eliminate_nil_morphism.
                            unfold compose.
                            rewrite tsubst_ltargument.
                            apply signed_refl.
                            apply space.(sstrefl).
                 **** unfold meliminate; unfold melimination; cbn.
                      intros [ parameter location | location ]; apply space.(sstvariance); intro parameter'; cbn.
                      ***** rewrite <- apply_eliminate_morphism.
                            rewrite eliminate_consid_pair_elimination.
                            rewrite eliminate_cons_pair_elimination.
                            rewrite eliminate_pair_morphism.
                            rewrite eliminate_extend_selection_pair_elimination.
                            rewrite eliminate_select_head_pair_elimination.
                            rewrite eliminate_nil_morphism.
                            unfold compose.
                            rewrite tsubst_ltargument.
                            apply signed_refl.
                            apply space.(sstrefl).
                      ***** rewrite <- apply_eliminate_morphism.
                            rewrite eliminate_consid_pair_elimination.
                            rewrite eliminate_cons_pair_elimination.
                            rewrite eliminate_pair_morphism.
                            rewrite eliminate_extend_selection_pair_elimination.
                            rewrite eliminate_select_head_pair_elimination.
                            rewrite eliminate_nil_morphism.
                            unfold compose.
                            rewrite tsubst_ltargument.
                            apply signed_refl.
                            apply space.(sstrefl).
                 **** intros [ ].
                 **** intros [ ].
                 **** intros [ ].
             *** apply mlactionv with listener interface hkeyed in receiver_vmodel.
                 apply gcmap_modelv.
                 rewrite eliminate_consid_pair_elimination.
                 unfold egci_reciever.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_id_morphism.
                 unfold compose.
                 assumption.
             *** specialize (argument_vmodel parameter).
                 apply mlactionv with listener interface hkeyed in argument_vmodel.
                 apply gcmap_modelv.
                 rewrite eliminate_consid_pair_elimination.
                 unfold egci_argument.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_pair_morphism.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_select_head_pair_elimination.
                 rewrite eliminate_extend_morphism_pair_elimination.
                 rewrite eliminate_id_morphism.
                 unfold compose.
                 assumption.
          ** cbn.
             intros [ | listener | parameter listener ]; simpl.
             *** destruct configuration as [ ? | ].
                 **** intros [ ].
                 **** trivial.
             *** apply receiver_vmodel.(munresolvedv).
             *** apply (argument_vmodel parameter).(munresolvedv).
  + clear c.
    rename s into body_sub.
    rename H into IHbodies.
    apply (projectiveSD2 (SCSetContains methods)) in IHbodies.
    destruct IHbodies as [ body_history consistent_body_history IHbodies ].
    apply (projectiveSD (SCSetContains methods)) in IHbodies.
    destruct IHbodies as [ body_model body_vmodel ].
    specialize (fun method contains => body_vmodel method contains _ (space.(sstrefl) _)).
    pose (fun listener: EGCobjectListener interface methods (fun method contains => egraphicalcore (bodies method contains)) => match listener with
          | egcolbody_nested method contains listener => (body_history method contains).(GCHKeyedS) listener
          end) as objectGCHKeyedS.
    pose (fun listener: EGCobjectListener interface methods (fun method contains => egraphicalcore (bodies method contains)) => match listener with
          | egcolbody_nested method contains listener => (body_history method contains).(GCHUnResolvedS) listener
          end) as objectGCHUnResolvedS.
    assert (forall listener interface, objectGCHKeyedS listener interface -> EGCobjectKeyedS listener interface) as objectgchkeyed by (intros [ method contains ] ?; apply (body_history method contains).(gchkeyed)).
    pose (fun listener: EGCobjectListener interface methods (fun method contains => egraphicalcore (bodies method contains)) => match listener as listener return forall interface hkeyed, GCHistory (EGCobjectAction listener interface (objectgchkeyed listener interface hkeyed)) with
                          | egcolbody_nested method contains listener => fun interface hkeyed => gcmap_history _ ((body_history method contains).(gchaction) listener interface hkeyed)
                          end) as objectgchaction.
    pose (Build_GCHistory _ (EGCobject interface methods (fun method contains => egraphicalcore (bodies method contains)))
                          objectGCHKeyedS
                          objectGCHUnResolvedS
                          objectgchkeyed
                          objectgchaction) as objecthistory.
    exists objecthistory.
    - constructor; intros [ method contains listener ].
      * apply (consistent_body_history method contains).(fgchunique).
      * apply (consistent_body_history method contains).(fgchunresolved).
      * apply (consistent_body_history method contains).(fgchresolved).
      * intros.
        apply final_gcmap_history.
        apply (consistent_body_history method contains).(fgchaction).
    - exists (Build_Model _ _ objecthistory space
                              (fun abstract => match abstract with
                                               | egcoaparameter parameter => arguments parameter
                                               | egcoainput method contains parameter => (signatures method contains).(smsinput) parameter
                                               | egcoaresult method contains => (signatures method contains).(smsresult)
                                               | egcoabody_nested method contains abstract => (body_model method contains).(mabstract) abstract
                                               end)
                              (fun listener => match listener with
                                               | egcolbody_nested method contains listener => (body_model method contains).(mlistener) listener
                                               end)
                              (fun node => match node with
                                           | egconobject => space.(stinterface) interface arguments
                                           | egconinput method contains parameter location => space.(stinterface) (linterface location) (fun parameter => tsubst arguments (ltargument location parameter))
                                           | egconresult method contains location => space.(stinterface) (linterface location) (fun parameter => tsubst arguments (ltargument location parameter))
                                           | egconbody_nested method contains node => (body_model method contains).(mnode) node
                                           end)
                              (fun listener => match listener as listener return forall interface (hkeyed: objectGCHKeyedS listener interface), scheme.(IParameter) interface -> space.(SpaceType) with
                                               | egcolbody_nested method contains listener => fun interface hkeyed => (body_model method contains).(mlargument) listener interface hkeyed
                                               end)
                              (fun listener => match listener as listener return forall interface hkeyed, Model (objectgchaction listener interface hkeyed) space with
                                               | egcolbody_nested method contains listener => fun interface hkeyed => gcmap_model _ ((body_model method contains).(mlaction) listener interface hkeyed)
                                               end)).
      intros result' subresult.
      constructor.
      * intros [ | method contains contains' parameter | method contains contains' | method contains constraint ]; unfold meliminatel; unfold meliminationl; unfold meliminate; unfold melimination; cbn.
        ** exact subresult.
        ** rewrite <- apply_eliminate_morphism.
           rewrite eliminate_consid_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           rewrite eliminate_nil_morphism.
           unfold compose.
           rewrite <- tsubst_tlocation.
           apply ((body_sub.(ssbsmethod) method contains').(ssmsinput) parameter).
        ** rewrite <- apply_eliminate_morphism.
           rewrite eliminate_consid_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           rewrite eliminate_nil_morphism.
           unfold compose.
           rewrite <- tsubst_tlocation.
           apply (body_sub.(ssbsmethod) method contains').(ssmsresult).
        ** rewrite <- apply_eliminate_morphism.
           rewrite <- apply_eliminate_morphism.
           rewrite eliminate_cons_pair_elimination.
           unfold egco_body_node.
           rewrite eliminate_consid_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           unfold egco_body.
           rewrite eliminate_pair_morphism.
           rewrite eliminate_select_head_pair_elimination.
           rewrite eliminate_pair_morphism.
           rewrite eliminate_select_head_pair_elimination.
           rewrite eliminate_pair_morphism.
           rewrite eliminate_select_head_pair_elimination.
           rewrite eliminate_extend_morphism_pair_elimination.
           rewrite eliminate_extend_morphism_pair_elimination.
           rewrite eliminate_id_morphism.
           unfold compose.
           apply (body_vmodel method contains).(mconstraintv).
      * intros [ | method contains parameter location | method contains location | method contains node ]; unfold meliminate; unfold melimination; cbn.
        ** apply sstrefl.
        ** apply sstvariance.
           intro.
           rewrite <- apply_eliminate_morphism.
           rewrite eliminate_consid_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           rewrite eliminate_nil_morphism.
           unfold compose.
           rewrite <- tsubst_ltargument.
           apply signed_refl.
           apply sstrefl.
        ** apply sstvariance.
           intro.
           rewrite <- apply_eliminate_morphism.
           rewrite eliminate_consid_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           rewrite eliminate_nil_morphism.
           unfold compose.
           rewrite <- tsubst_ltargument.
           apply signed_refl.
           apply sstrefl.
        ** eapply ssttrans; try apply (body_vmodel method contains).(mlowerv).
           apply sstvariance.
           intro.
           rewrite <- apply_eliminate_morphism.
           unfold egco_body_node.
           rewrite eliminate_consid_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           unfold egco_body.
           rewrite eliminate_pair_morphism.
           rewrite eliminate_select_head_pair_elimination.
           rewrite eliminate_pair_morphism.
           rewrite eliminate_select_head_pair_elimination.
           rewrite eliminate_pair_morphism.
           rewrite eliminate_select_head_pair_elimination.
           rewrite eliminate_extend_morphism_pair_elimination.
           rewrite eliminate_extend_morphism_pair_elimination.
           rewrite eliminate_id_morphism.
           unfold compose.
           apply signed_refl.
           apply sstrefl.
      * intros [ | method contains parameter location | method contains location | method contains node ]; unfold meliminate; unfold melimination; cbn.
        ** apply sstrefl.
        ** apply sstvariance.
           intro.
           rewrite <- apply_eliminate_morphism.
           rewrite eliminate_consid_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           rewrite eliminate_nil_morphism.
           unfold compose.
           rewrite <- tsubst_ltargument.
           apply signed_refl.
           apply sstrefl.
        ** apply sstvariance.
           intro.
           rewrite <- apply_eliminate_morphism.
           rewrite eliminate_consid_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           rewrite eliminate_nil_morphism.
           unfold compose.
           rewrite <- tsubst_ltargument.
           apply signed_refl.
           apply sstrefl.
        ** eapply ssttrans; try apply (body_vmodel method contains).(mupperv).
           apply sstvariance.
           intro.
           rewrite <- apply_eliminate_morphism.
           unfold egco_body_node.
           rewrite eliminate_consid_pair_elimination.
           rewrite eliminate_cons_pair_elimination.
           unfold egco_body.
           rewrite eliminate_pair_morphism.
           rewrite eliminate_select_head_pair_elimination.
           rewrite eliminate_pair_morphism.
           rewrite eliminate_select_head_pair_elimination.
           rewrite eliminate_pair_morphism.
           rewrite eliminate_select_head_pair_elimination.
           rewrite eliminate_extend_morphism_pair_elimination.
           rewrite eliminate_extend_morphism_pair_elimination.
           rewrite eliminate_id_morphism.
           unfold compose.
           apply signed_refl.
           apply sstrefl.
      * intros [ method contains listener ]; cbn.
        apply (body_vmodel method contains).(mlargumentv).
      * intros [ method contains listener ]; cbn.
        intros ? hkeyed.
        apply gcmap_modelv.
        rewrite eliminate_consid_pair_elimination.
        unfold egco_body.
        rewrite eliminate_pair_morphism.
        rewrite eliminate_select_head_pair_elimination.
        rewrite eliminate_pair_morphism.
        rewrite eliminate_select_head_pair_elimination.
        rewrite eliminate_pair_morphism.
        rewrite eliminate_select_head_pair_elimination.
        rewrite eliminate_extend_morphism_pair_elimination.
        rewrite eliminate_extend_morphism_pair_elimination.
        rewrite eliminate_id_morphism.
        apply (body_vmodel method contains).(mlactionv).
      * intros [ method contains listener ]; cbn.
        apply (body_vmodel method contains).(munresolvedv).
Qed.



(* Part 11.4: Type-Checkability *)

(* ExpressionValidS defines type-checkability of an expression.
 * The definition here is equivalent to that of Figure 17 of the paper, but it is defined recursively rather than inductively.
 *)
Definition ExpressionValidS: forall {Input: Sort}, Expression Input -> SProp
:= fix ExpressionValidS {Input: Sort} (expression: Expression Input) {struct expression}: SProp
:= match expression with
   | einput input => TrueS
   | einvoke receiver method arguments => AndS (ExpressionValidS receiver)
                                               (forall input: scheme.(MInput) method, ExpressionValidS (arguments input))
   | eobject interface methods bodies => AndS (forall method: scheme.(Method), SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method -> SCSetContains methods method)
                                              (forall method: scheme.(Method), forall contains: SCSetContains methods method, ExpressionValidS (bodies method contains))
   end.

(* Here we prove Lemma 9.2 of the paper: that if there exists a type space that an expression can type-check within, then the expression is type-checkable. *)
Lemma check_valid {Input: Sort} {expression: Expression Input} (space: TypeSpace) (context: SortElimination space.(SpaceType) Input) (type: space.(SpaceType)): CheckExpression space context expression type -> ExpressionValidS expression.
Proof.
  intro check.
  induction check; simpl.
  + assumption.
  + constructor.
  + split; assumption.
  + split; try assumption.
    apply s.(ssbsmethods).
Qed.



(* Part 11.5: Soundness of Extraction from an Expression
 * Here we prove the if direction of Lemma 9.1: if a type space models an expression's extracted graphical core, then the expression type-checks within that type space.
 *)

(* The proof will proceed by induction.
 * As such, in order to establish that the expression type-checks within the given type space modeling its extracted graphical core, we will need need to demonstrate that that type space also models its subexpressions' extracted graphical cores.
 * Of course, extraction works by construction a graphical core that contains each of these subexpressions' graphical cores.
 * Thus, a model of the outer graphical core inherently models these nested graphical cores.
 * We establish formally using morphisms of graphical core: the extracted graphical cores of the subexpressions each have a morphism to the outer extracted graphical core, and we can compose each such morphism with the outer model to get a model of each nested graphical core.
 * Here we define graphical cores in two parts: the functions mapping between components of the graphical cores, and a predicate requiring those functions to preserve the structure of graphical cores in the obvious manner.
 *)
CoInductive GCMorphism {Transitive Transitive': Sort} {core: GraphicalCore Transitive} {core': GraphicalCore Transitive'}: Type :=
{ gcmabstract: core.(GCAbstract) -> core'.(GCAbstract);
  gcmlistener: core.(GCListener) -> core'.(GCListener);
  gcmnode: core.(GCNode) -> core'.(GCNode);
  gcmconstraint: core.(GCConstraint) -> core'.(GCConstraint);
  gcmninterface (node: core.(GCNode)): eqS (core.(gcninterface) node) (core'.(gcninterface) (gcmnode node));
  gcmkeyed {listener: core.(GCListener)} {interface: scheme.(Interface)}: core.(GCLKeyedS) listener interface -> core'.(GCLKeyedS) (gcmlistener listener) interface;
  gcmaction (listener: core.(GCListener)) (interface: scheme.(Interface)) (keyed: core.(GCLKeyedS) listener interface): GCMorphism (core := core.(gclaction) listener interface keyed) (core' := core'.(gclaction) (gcmlistener listener) interface (gcmkeyed keyed));
}.
Arguments GCMorphism {_ _} _ _.
CoInductive GCMorphismV `{SSet scheme.(Interface)} {Transitive Transitive': Sort} {core: GraphicalCore Transitive} {core': GraphicalCore Transitive'} {vmap: SortMorphism Transitive (cons core'.(GCAbstract) Transitive')} {morphism: GCMorphism core core'}: Prop :=
{ gcmvnargument (node: core.(GCNode)) (parameter: scheme.(IParameter) (core.(gcninterface) node)): apply_morphism (consid_morphism Unit (cons_morphism morphism.(gcmnode) (pair_morphism (select_head morphism.(gcmabstract)) vmap))) (core.(gcnargument) node parameter) = core'.(gcnargument) (morphism.(gcmnode) node) (convert (morphism.(gcmninterface) node) scheme.(IParameter) parameter);
  gcmvclower (constraint: core.(GCConstraint)): apply_morphism (consid_morphism Unit (cons_morphism morphism.(gcmnode) (pair_morphism (select_head morphism.(gcmabstract)) vmap))) (core.(gcclower) constraint) = core'.(gcclower) (morphism.(gcmconstraint) constraint);
  gcmvcupper (constraint: core.(GCConstraint)): apply_morphism (cons_morphism morphism.(gcmlistener) (consid_morphism Unit (cons_morphism morphism.(gcmnode) (pair_morphism (select_head morphism.(gcmabstract)) vmap)))) (core.(gccupper) constraint) = core'.(gccupper) (morphism.(gcmconstraint) constraint);
  gcmvaction (listener: core.(GCListener)) (interface: scheme.(Interface)) (keyed: core.(GCLKeyedS) listener interface): GCMorphismV (vmap := extend_morphism _ (consid_morphism (scheme.(IParameter) interface) (pair_morphism (select_head morphism.(gcmabstract)) vmap))) (morphism := morphism.(gcmaction) listener interface keyed);
}.
Arguments GCMorphismV {_ _ _ _ _} _ _.

Definition gcmap_morphism: forall {Transitive Transitive': Sort} (vmap: SortMorphism Transitive Transitive') (core: GraphicalCore Transitive), GCMorphism core (gcmap vmap core)
:= cofix gcmap_morphism {Transitive Transitive': Sort} (vmap: SortMorphism Transitive Transitive') (core: GraphicalCore Transitive): GCMorphism core (gcmap vmap core)
:= Build_GCMorphism Transitive Transitive' core (gcmap vmap core)
                    (fun abstract => abstract)
                    (fun listener => listener)
                    (fun node => node)
                    (fun constraint => constraint)
                    (fun node => eqS_refl (core.(gcninterface) node))
                    (fun listener interface keyed => keyed)
                    (fun listener interface keyed => gcmap_morphism _ (core.(gclaction) listener interface keyed)).
Lemma gcmap_morphismv {Interface_SSet: SSet scheme.(Interface)}: forall {Transitive Transitive': Sort} (vmap: SortMorphism Transitive Transitive') (core: GraphicalCore Transitive), GCMorphismV (extend_morphism (gcmap vmap core).(GCAbstract) vmap) (gcmap_morphism vmap core).
Proof.
  cofix gcmap_morphismv.
  intros.
  constructor; intros.
  + rewrite convert_id.
    reflexivity.
  + reflexivity.
  + trivial.
  + exact (gcmap_morphismv _ _ _ _).
Qed.



(* A morphism including a nested graphical core into an outer graphical core satisfies an additional property that it reflects some of the structure of a graphical core.
 * In particular, if a mapped listener has an event for some interface in the target graphical core, then the original listener also has an event for the same interface in the source graphical core.
 *)
CoInductive GCReflectsS {Transitive Transitive': Sort} {core: GraphicalCore Transitive} {core': GraphicalCore Transitive'} {morphism: GCMorphism core core'}: SProp :=
{ gcrkeyed (listener: core.(GCListener)) (interface: scheme.(Interface)) (keyed': core'.(GCLKeyedS) (morphism.(gcmlistener) listener) interface): core.(GCLKeyedS) listener interface;
  gcrlaction (listener: core.(GCListener)) (interface: scheme.(Interface)) (keyed: core.(GCLKeyedS) listener interface): GCReflectsS (morphism := morphism.(gcmaction) listener interface keyed);
}.
Arguments GCReflectsS {_ _ _ _} _.

Lemma gcmap_morphismr {Interface_SSet: SSet scheme.(Interface)}: forall {Transitive Transitive': Sort} (tmap: SortMorphism Transitive Transitive') (core: GraphicalCore Transitive), GCReflectsS (gcmap_morphism tmap core).
Proof.
  cofix gcmap_morphismr.
  intros Transitive Transitive' tmap core.
  constructor; cbn; intros.
  + assumption.
  + apply gcmap_morphismr.
Qed.



(* Given a history defined on the target of some graphical core morphism, we can construct a history on the source graphical core of the morphism as well in the obivous manner. *)
Definition gcprehistory: forall {Transitive Transitive': Sort} {core: GraphicalCore Transitive} {core': GraphicalCore Transitive'} (morphism: GCMorphism core core'), GCHistory core' -> GCHistory core
:= cofix gcprehistory {Transitive Transitive': Sort} {core: GraphicalCore Transitive} {core': GraphicalCore Transitive'} (morphism: GCMorphism core core') (history': GCHistory core'): GCHistory core :=
{| GCHKeyedS listener interface := AndS (core.(GCLKeyedS) listener interface) (history'.(GCHKeyedS) (morphism.(gcmlistener) listener) interface);
   GCHUnResolvedS listener := history'.(GCHUnResolvedS) (morphism.(gcmlistener) listener);
   gchkeyed listener interface hkeyed := hkeyed.(proj1_AndS);
   gchaction listener interface hkeyed := gcprehistory (morphism.(gcmaction) listener interface hkeyed.(proj1_AndS)) (history'.(gchaction) (morphism.(gcmlistener) listener) interface hkeyed.(proj2_AndS));
|}.
(* This gcprehistory is final if the original history is final and the morphism is reflective. *)
Lemma final_gcprehistory: forall {Transitive Transitive': Sort} {core: GraphicalCore Transitive} {core': GraphicalCore Transitive'} (morphism: GCMorphism core core') (history: GCHistory core'), FinalGCHistory history -> GCReflectsS morphism -> FinalGCHistory (gcprehistory morphism history).
Proof.
  cofix final_gcprehistory.
  intros Transitive Transitive' core core' morphism history final reflects.
  constructor; cbn.
  + intros listener interface interface' [ keyed hkeyed ] [ keyed' hkeyed' ].
    apply (final.(fgchunique) hkeyed) in hkeyed'.
    assumption.
  + intros listener ur interface [ keyed hkeyed ].
    eapply final.(fgchunresolved); eassumption.
  + intro listener.
    destruct final.(fgchresolved) with (morphism.(gcmlistener) listener) as [ ? | [ interface ? ] ].
    - left.
      assumption.
    - right.
      exists interface.
      split; try assumption.
      apply reflects.(gcrkeyed).
      apply history.(gchkeyed).
      assumption.
  + intros listener interface [ keyed hkeyed ].
    cbn.
    apply final_gcprehistory.
    - apply (final.(fgchaction) _ _ hkeyed).
    - apply reflects.(gcrlaction).
Qed.



(* Here we establish that morphisms compose with models to form models. *)
Definition compose_model {space: TypeSpace}: forall {Transitive Transitive': Sort} {core: GraphicalCore Transitive} {core': GraphicalCore Transitive'} (morphism: GCMorphism core core') {history': GCHistory core'}, Model history' space -> Model (gcprehistory morphism history') space
:= cofix compose_model {Transitive Transitive': Sort} {core: GraphicalCore Transitive} {core': GraphicalCore Transitive'} (morphism: GCMorphism core core') {history': GCHistory core'} (model': Model history' space): Model (gcprehistory morphism history') space :=
{| mabstract := compose morphism.(gcmabstract) model'.(mabstract);
   mlistener := compose morphism.(gcmlistener) model'.(mlistener);
   mnode := compose morphism.(gcmnode) model'.(mnode);
   mlargument listener interface (hkeyed: (gcprehistory morphism history').(GCHKeyedS) listener interface) := model'.(mlargument) (morphism.(gcmlistener) listener) interface hkeyed.(proj2_AndS);
   mlaction listener interface hkeyed := compose_model (morphism.(gcmaction) listener interface ((gcprehistory morphism history').(gchkeyed) hkeyed)) (model'.(mlaction) (morphism.(gcmlistener) listener) interface hkeyed.(proj2_AndS));
|}.
Lemma compose_modelv {Interface_SSet: SSet scheme.(Interface)} {space: TypeSpace}: forall {Transitive Transitive': Sort} {core: GraphicalCore Transitive} {core': GraphicalCore Transitive'} (morphism: GCMorphism core core') (history': GCHistory core') (model': Model history' space) (tmap: SortMorphism Transitive (cons core'.(GCAbstract) Transitive')) (elimination: SortElimination space.(SpaceType) Transitive'), GCMorphismV tmap morphism -> ModelV model' elimination -> ModelV (compose_model morphism model') (eliminate_morphism tmap (pair_elimination model'.(mabstract) elimination)).
Proof.
  cofix compose_modelv.
  intros Transitive Transitive' core core' morphism history' model' tmap elimination vmorphism vmodel'.
  constructor.
  + intro constraint.
    pose proof (vmodel'.(mconstraintv) (morphism.(gcmconstraint) constraint)) as sub.
    rewrite <- vmorphism.(gcmvclower) in sub.
    rewrite <- vmorphism.(gcmvcupper) in sub.
    unfold meliminate in *.
    unfold meliminatel in *.
    rewrite <- apply_eliminate_morphism in sub.
    rewrite <- apply_eliminate_morphism in sub.
    unfold meliminationl in *.
    rewrite eliminate_cons_pair_elimination in sub.
    unfold melimination in *.
    rewrite eliminate_consid_pair_elimination in sub.
    rewrite eliminate_cons_pair_elimination in sub.
    rewrite eliminate_pair_morphism in sub.
    rewrite eliminate_select_head_pair_elimination in sub.
    assumption.
  + intro node.
    change ((compose_model morphism model').(mnode) node) with (model'.(mnode) (morphism.(gcmnode) node)).
    eapply ssttrans; try apply vmodel'.(mlowerv).
    apply sstvariance_eqS with (morphism.(gcmninterface) node).
    intro parameter.
    rewrite <- vmorphism.(gcmvnargument).
    unfold meliminate.
    rewrite <- apply_eliminate_morphism.
    unfold melimination.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_pair_morphism.
    rewrite eliminate_select_head_pair_elimination.
    apply signed_refl.
    apply sstrefl.
  + intro node.
    change ((compose_model morphism model').(mnode) node) with (model'.(mnode) (morphism.(gcmnode) node)).
    eapply ssttrans; try apply vmodel'.(mupperv).
    apply sstvariance_eqS' with (morphism.(gcmninterface) node).
    intro parameter.
    rewrite <- vmorphism.(gcmvnargument).
    unfold meliminate.
    rewrite <- apply_eliminate_morphism.
    unfold melimination.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_pair_morphism.
    rewrite eliminate_select_head_pair_elimination.
    apply signed_refl.
    apply sstrefl.
  + intros listener interface [ keyed hkeyed ].
    cbn.
    apply vmodel'.(mlargumentv).
  + intros listener interface [ keyed hkeyed ].
    cbn.
    specialize (compose_modelv _ _ _ _ (morphism.(gcmaction) listener interface keyed) _ (model'.(mlaction) (morphism.(gcmlistener) listener) interface hkeyed)).
    specialize (compose_modelv (extend_morphism _ (consid_morphism _ (pair_morphism (select_head morphism.(gcmabstract)) tmap)))).
    specialize (compose_modelv (pair_elimination (model'.(mlargument) (morphism.(gcmlistener) listener) interface hkeyed) (pair_elimination model'.(mabstract) elimination))).
    specialize (fun vmorphism => compose_modelv vmorphism (vmodel'.(mlactionv) (morphism.(gcmlistener) listener) interface hkeyed)).
    rewrite eliminate_extend_morphism_pair_elimination in compose_modelv.
    rewrite eliminate_consid_pair_elimination in compose_modelv.
    rewrite eliminate_pair_morphism in compose_modelv.
    rewrite eliminate_select_head_pair_elimination in compose_modelv.
    apply compose_modelv; clear compose_modelv.
    apply vmorphism.(gcmvaction).
  + cbn.
    unfold compose.
    intros listener ur.
    apply vmodel'.(munresolvedv).
    assumption.
Qed.



(* The following define and validate the morphisms from the graphical cores extracted from various subexpressions to the graphical core extracted from their respective containing expression. *)
Definition gcminvoke_receiver {Input: Sort} (receiver: EGraphicalCore Input) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input): GCMorphism receiver (EGCinvoke receiver method arguments)
:= Build_GCMorphism _ _ receiver (EGCinvoke receiver method arguments)
                    egciareceiver_nested
                    egcilreceiver_nested
                    egcinreceiver_nested
                    egcicreceiver_nested
                    (fun node => eqS_refl (receiver.(gcninterface) node))
                    (fun listener interface keyed => keyed)
                    (fun listener interface keyed => gcmap_morphism _ (receiver.(gclaction) listener interface keyed)).
Lemma gcminvoke_receiverv {Interface_SSet: SSet scheme.(Interface)} {Input: Sort} (receiver: EGraphicalCore Input) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input): GCMorphismV (core' := EGCinvoke receiver method arguments) (pair_morphism (select_head (fun _ => egciareceiver)) (extend_morphism _ (extend_morphism _ id_morphism))) (gcminvoke_receiver receiver method arguments).
Proof.
  constructor; intros.
  + rewrite convert_id.
    reflexivity.
  + reflexivity.
  + reflexivity.
  + apply gcmap_morphismv.
Qed.
Lemma gcminvoke_receiverr {Interface_SSet: SSet scheme.(Interface)} {Input: Sort} (receiver: EGraphicalCore Input) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input): GCReflectsS (core' := EGCinvoke receiver method arguments) (gcminvoke_receiver receiver method arguments).
Proof.
  constructor; cbn; intros.
  + assumption.
  + apply gcmap_morphismr.
Qed.

Definition gcminvoke_argument {Input: Sort} (receiver: EGraphicalCore Input) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input) (parameter: scheme.(MInput) method): GCMorphism (arguments parameter) (EGCinvoke receiver method arguments)
:= Build_GCMorphism _ _ (arguments parameter) (EGCinvoke receiver method arguments)
                    (egciaargument_nested parameter)
                    (egcilargument_nested parameter)
                    (egcinargument_nested parameter)
                    (egcicargument_nested parameter)
                    (fun node => eqS_refl ((arguments parameter).(gcninterface) node))
                    (fun listener interface keyed => keyed)
                    (fun listener interface keyed => gcmap_morphism _ ((arguments parameter).(gclaction) listener interface keyed)).
Lemma gcminvoke_argumentv {Interface_SSet: SSet scheme.(Interface)} {Input: Sort} (receiver: EGraphicalCore Input) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input) (parameter: scheme.(MInput) method): GCMorphismV (core' := EGCinvoke receiver method arguments) (pair_morphism (select_head (fun _ => egciaargument parameter)) (extend_morphism _ (extend_morphism _ id_morphism))) (gcminvoke_argument receiver method arguments parameter).
Proof.
  constructor; intros.
  + rewrite convert_id.
    reflexivity.
  + reflexivity.
  + reflexivity.
  + apply gcmap_morphismv.
Qed.
Lemma gcminvoke_argumentr {Interface_SSet: SSet scheme.(Interface)} {Input: Sort} (receiver: EGraphicalCore Input) (method: scheme.(Method)) (arguments: scheme.(MInput) method -> EGraphicalCore Input) (parameter: scheme.(MInput) method): GCReflectsS (core' := EGCinvoke receiver method arguments) (gcminvoke_argument receiver method arguments parameter).
Proof.
  constructor; cbn; intros.
  + assumption.
  + apply gcmap_morphismr.
Qed.

Definition gcmobject_body {Input: Sort} (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)) (method: scheme.(Method)) (contains: SCSetContains methods method): GCMorphism (bodies method contains) (EGCobject interface methods bodies)
:= Build_GCMorphism _ _ (bodies method contains) (EGCobject interface methods bodies)
                    (egcoabody_nested method contains)
                    (egcolbody_nested method contains)
                    (egconbody_nested method contains)
                    (egcocbody_nested method contains)
                    (fun node => eqS_refl ((bodies method contains).(gcninterface) node))
                    (fun listener interface keyed => keyed)
                    (fun listener interface keyed => gcmap_morphism _ ((bodies method contains).(gclaction) listener interface keyed)).
Lemma gcmobject_bodyv {Interface_SSet: SSet scheme.(Interface)} {Input: Sort} (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)) (method: scheme.(Method)) (contains: SCSetContains methods method): GCMorphismV (core' := EGCobject interface methods bodies) (pair_morphism (select_head (fun _ => egcoaresult method contains)) (pair_morphism (select_head (fun parameter => egcoainput method contains parameter)) (extend_morphism _ (extend_morphism _ id_morphism)))) (gcmobject_body interface methods bodies method contains).
Proof.
  constructor; intros.
  + rewrite convert_id.
    reflexivity.
  + reflexivity.
  + reflexivity.
  + apply gcmap_morphismv.
Qed.
Lemma gcmobject_bodyr {Interface_SSet: SSet scheme.(Interface)} {Input: Sort} (interface: scheme.(Interface)) (methods: SCSet scheme.(Method)) (bodies: forall method: scheme.(Method), SCSetContains methods method -> EGraphicalCore (cons (scheme.(MInput) method) Input)) (method: scheme.(Method)) (contains: SCSetContains methods method): GCReflectsS (core' := EGCobject interface methods bodies) (gcmobject_body interface methods bodies method contains).
Proof.
  constructor; cbn; intros.
  + assumption.
  + apply gcmap_morphismr.
Qed.



(* Here we use the above morphism infrastructure to prove that if a type space models an expression's extracted graphical core the it can type-check the expression. *)
Lemma egraphicalcore_sound
      {Interface_SSet: SSet scheme.(Interface)}
      {Input: Sort}
      (expression: Expression Input)
      (history: GCHistory (egraphicalcore expression))
      (space: TypeSpace)
      (model: Model history space)
      (context: SortElimination space.(SpaceType) Input)
      (result: space.(SpaceType))
    : HierarchyV
   -> ExpressionValidS expression
   -> FinalGCHistory history
   -> ModelV model (pair_elimination (fun _ => result) context)
   -> CheckExpression space context expression result.
Proof.
  intros vhierarchy vexpression final vmodel.
  revert result vmodel; induction expression as [ Input input | Input receiver IHreceiver method arguments IHarguments | Input interface methods bodies IHbodies ]; intros result vmodel.
  + apply cesub with (apply_elimination context input); try apply ceinput.
    apply (vmodel.(mconstraintv) tt).
  + apply ceinvoke_sub with (model.(mabstract) egciareceiver) (fun parameter => model.(mabstract) (egciaargument parameter)).
    - destruct (final.(fgchresolved) egcilreceiver) as [ ur | [ interface hkeyed ] ].
      * exists (model.(mlistener) egcilreceiver); try apply (vmodel.(mconstraintv) egcicreceiver).
        eexists; try apply ssmsrefl.
        apply cmunreachable.
        apply vmodel.(munresolvedv).
        assumption.
      * exists (space.(stinterface) interface (model.(mlargument) _ _ hkeyed)).
        ** eapply ssttrans; try eassumption.
           apply (vmodel.(mconstraintv) egcicreceiver).
           apply vmodel.(mlargumentv).
        ** exists (mssubst (model.(mlargument) _ _ hkeyed) ((hierarchy.(hinterface) interface).(uisbody).(ubsmethod) method (history.(gchkeyed) hkeyed))); try apply cminterface.
           constructor; cbn.
           *** intro parameter.
               eapply ssttrans; try apply ((vmodel.(mlactionv) _ _ hkeyed).(mconstraintv) (egciacargument parameter)).
               cbn.
               unfold meliminatel.
               unfold meliminationl.
               rewrite <- apply_eliminate_morphism.
               unfold melimination.
               rewrite eliminate_consid_pair_elimination.
               rewrite eliminate_cons_pair_elimination.
               rewrite eliminate_pair_morphism.
               rewrite eliminate_extend_selection_pair_elimination.
               rewrite eliminate_nil_morphism.
               eapply (msubstv_upper (model.(mlaction) egcilreceiver interface hkeyed) (pair_elimination (model.(mlargument) _ _ hkeyed) (pair_elimination model.(mabstract) (pair_elimination (fun _ => result) context))) (extend_selection _ (select_head (fun parameter => parameter)))) with (einterface := fun parameter => eqS_refl _); try apply vmodel.(mlactionv).
               intros location parameter'.
               rewrite convert_id.
               reflexivity.
           *** eapply ssttrans; try apply ((vmodel.(mlactionv) _ _ hkeyed).(mconstraintv) egciacresult).
               cbn.
               unfold meliminate.
               rewrite <- apply_eliminate_morphism.
               unfold melimination.
               rewrite eliminate_consid_pair_elimination.
               rewrite eliminate_cons_pair_elimination.
               rewrite eliminate_pair_morphism.
               rewrite eliminate_extend_selection_pair_elimination.
               rewrite eliminate_nil_morphism.
               eapply (msubstv_lower (model.(mlaction) egcilreceiver interface hkeyed) (pair_elimination (model.(mlargument) _ _ hkeyed) (pair_elimination model.(mabstract) (pair_elimination (fun _ => result) context))) (extend_selection _ (select_head (fun parameter => parameter)))) with (einterface := fun parameter => eqS_refl _); try apply vmodel.(mlactionv).
               intros location parameter'.
               rewrite convert_id.
               reflexivity.
    - set (morphism := gcminvoke_receiver (egraphicalcore receiver) _ (fun parameter => egraphicalcore (arguments parameter))).
      pose proof (gcminvoke_receiverv (egraphicalcore receiver) _ (fun parameter => egraphicalcore (arguments parameter))) as vmorphism.
      pose proof (gcminvoke_receiverr (egraphicalcore receiver) _ (fun parameter => egraphicalcore (arguments parameter))) as rmorphism.
      apply IHreceiver with (gcprehistory morphism history) (compose_model morphism model).
      * apply vexpression.
      * apply final_gcprehistory; assumption.
      * pose proof (compose_modelv morphism history model _ _ vmorphism vmodel) as vmodel'.
        rewrite eliminate_pair_morphism in vmodel'.
        rewrite eliminate_select_head_pair_elimination in vmodel'.
        rewrite eliminate_extend_morphism_pair_elimination in vmodel'.
        rewrite eliminate_extend_morphism_pair_elimination in vmodel'.
        rewrite eliminate_id_morphism in vmodel'.
        assumption.
    - intro parameter.
      set (morphism := gcminvoke_argument (egraphicalcore receiver) _ (fun parameter => egraphicalcore (arguments parameter)) parameter).
      pose proof (gcminvoke_argumentv (egraphicalcore receiver) _ (fun parameter => egraphicalcore (arguments parameter)) parameter) as vmorphism.
      pose proof (gcminvoke_argumentr (egraphicalcore receiver) _ (fun parameter => egraphicalcore (arguments parameter)) parameter) as rmorphism.
      apply IHarguments with (gcprehistory morphism history) (compose_model morphism model).
      * apply vexpression.
      * apply final_gcprehistory; assumption.
      * pose proof (compose_modelv morphism history model _ _ vmorphism vmodel) as vmodel'.
        rewrite eliminate_pair_morphism in vmodel'.
        rewrite eliminate_select_head_pair_elimination in vmodel'.
        rewrite eliminate_extend_morphism_pair_elimination in vmodel'.
        rewrite eliminate_extend_morphism_pair_elimination in vmodel'.
        rewrite eliminate_id_morphism in vmodel'.
        assumption.
  + apply cesub with (model.(mnode) egconobject); try apply (vmodel.(mconstraintv) egcocobject).
    apply cesub with (space.(stinterface) interface (compose egcoaparameter model.(mabstract))); try apply (vmodel.(mlowerv) egconobject).
    apply ceobject with (fun method contains => {| smsinput input := model.(mabstract) (egcoainput method contains input); smsresult := model.(mabstract) (egcoaresult method contains) |}).
    - destruct vexpression as [ covers vexpression ].
      exists covers.
      intros method contains.
      cbn in contains.
      constructor; cbn.
      * intro parameter.
        eapply ssttrans; try apply (vmodel.(mconstraintv) (egcocinput method (covers method contains) contains parameter)).
        cbn.
        unfold meliminate.
        rewrite <- apply_eliminate_morphism.
        unfold melimination.
        rewrite eliminate_consid_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        rewrite eliminate_nil_morphism.
        eapply (msubstv_lower model (pair_elimination (fun _ => result) context) (select_head egcoaparameter)) with (einterface := fun parameter => eqS_refl _); try eassumption.
        intros location parameter'.
        rewrite convert_id.
        reflexivity.
      * eapply ssttrans; try apply (vmodel.(mconstraintv) (egcocresult method (covers method contains) contains)).
        cbn.
        unfold meliminatel.
        unfold meliminationl.
        rewrite <- apply_eliminate_morphism.
        unfold melimination.
        rewrite eliminate_consid_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        rewrite eliminate_nil_morphism.
        eapply (msubstv_upper model (pair_elimination (fun _ => result) context) (select_head egcoaparameter)) with (einterface := fun parameter => eqS_refl _); try eassumption.
        intros location parameter'.
        rewrite convert_id.
        reflexivity.
    - cbn.
      intros method contains.
      set (morphism := gcmobject_body interface methods (fun method contains => egraphicalcore (bodies method contains)) method contains).
      pose proof (gcmobject_bodyv interface methods (fun method contains => egraphicalcore (bodies method contains)) method contains) as vmorphism.
      pose proof (gcmobject_bodyr interface methods (fun method contains => egraphicalcore (bodies method contains)) method contains) as rmorphism.
      apply IHbodies with (gcprehistory morphism history) (compose_model morphism model).
      * apply vexpression.
      * apply final_gcprehistory; assumption.
      * pose proof (compose_modelv morphism history model _ _ vmorphism vmodel) as vmodel'.
        rewrite eliminate_pair_morphism in vmodel'.
        rewrite eliminate_select_head_pair_elimination in vmodel'.
        rewrite eliminate_pair_morphism in vmodel'.
        rewrite eliminate_select_head_pair_elimination in vmodel'.
        rewrite eliminate_extend_morphism_pair_elimination in vmodel'.
        rewrite eliminate_extend_morphism_pair_elimination in vmodel'.
        rewrite eliminate_id_morphism in vmodel'.
        assumption.
Qed.



(* Part 11.6: Closed Types
 * The following prove a few straightforward properties about closed types.
 *)

Lemma uv_closed (type: UserType Empty): forall variance: Empty -> Sign, forall sign: Sign, UserVariance variance type sign.
Proof.
  induction type; intros variance sign.
  + destruct variable.
  + apply uvany.
  + apply uvinterface.
    auto.
Qed.

Lemma tsubst_closed (type: UserType Empty): forall space: TypeSpace, forall substitution substitution': Empty -> space.(SpaceType), space.(SubSpaceType) (tsubst substitution type) (tsubst substitution' type).
Proof.
  intros space substitution substitution'.
  apply (tsubst_sub_tsubst positive) with emptye; try apply uv_closed.
  intros [ ].
Qed.

Lemma space_largument_closed (type: UserType Empty) (space: TypeSpace) (substitution substitution': Empty -> space.(SpaceType)) (location: Location type) (parameter: scheme.(IParameter) (linterface location)): apply_elimination (pair_elimination (fun _ => space.(stany)) (pair_elimination (fun location => space.(stinterface) (linterface location) (fun parameter => tsubst emptye (ltargument location parameter))) (pair_elimination substitution nil_elimination))) (largument location parameter) = apply_elimination (pair_elimination (fun _ => space.(stany)) (pair_elimination (fun location => space.(stinterface) (linterface location) (fun parameter => tsubst emptye (ltargument location parameter))) (pair_elimination substitution' nil_elimination))) (largument location parameter).
Proof.
  destruct (largument location parameter) as [ ? | [ ? | [ [ ] | [ ] ] ] ]; reflexivity.
Qed.



(* Part 11.7: The Graphical Core of a Program
 * The following extend the above constructions and proofs to programs.
 *)

Definition PGCAbstract (program: Program): Type
:= option (egraphicalcore program.(pexpression)).(GCAbstract).
Definition PGCNode (program: Program): Type
:= sum (egraphicalcore program.(pexpression)).(GCNode) (Location program.(ptype)).
Definition PGCListener (program: Program): Type
:= (egraphicalcore program.(pexpression)).(GCListener).
Definition PGCConstraint (program: Program): Type
:= option (egraphicalcore program.(pexpression)).(GCConstraint).
Definition pgcm_type (program: Program): SortMorphism (cons Unit (cons (Location program.(ptype)) (cons Empty nil))) (cons Unit (cons (PGCNode program) (cons (PGCAbstract program) nil)))
:= consid_morphism Unit (cons_morphism inr (cons_morphism emptye nil_morphism)).
Definition pgcm_expression (program: Program): SortMorphism (cons (egraphicalcore program.(pexpression)).(GCAbstract) (cons Unit nil)) (cons (PGCAbstract program) nil)
:= pair_morphism (select_head Some) (pair_morphism (select_head (fun _ => None)) nil_morphism).
Definition pgcm_expression_node (program: Program): SortMorphism (cons Unit (cons (egraphicalcore program.(pexpression)).(GCNode) (cons (egraphicalcore program.(pexpression)).(GCAbstract) (cons Unit nil)))) (cons Unit (cons (PGCNode program) (cons (PGCAbstract program) nil)))
:= consid_morphism Unit (cons_morphism inl (pgcm_expression program)).
Definition pgraphicalcore (program: Program): GraphicalCore nil :=
{| GCAbstract := PGCAbstract program;
   GCNode := PGCNode program;
   GCListener := PGCListener program;
   GCConstraint := PGCConstraint program;
   gcninterface := sume (egraphicalcore program.(pexpression)).(gcninterface) linterface;
   gcnargument node := match node with
                       | inl node => fun parameter => apply_morphism (pgcm_expression_node program) ((egraphicalcore program.(pexpression)).(gcnargument) node parameter)
                       | inr location => fun parameter => apply_morphism (pgcm_type program) (largument location parameter)
                       end;
   gcclower constraint := match constraint with
                          | Some constraint => apply_morphism (pgcm_expression_node program) ((egraphicalcore program.(pexpression)).(gcclower) constraint)
                          | None => sortr (sortr (sortl None))
                          end;
   gccupper constraint := match constraint with
                          | Some constraint => apply_morphism (consid_morphism (PGCListener program) (pgcm_expression_node program)) ((egraphicalcore program.(pexpression)).(gccupper) constraint)
                          | None => sortr (apply_morphism (pgcm_type program) (tlocation program.(ptype)))
                          end;
   GCLKeyedS := (egraphicalcore program.(pexpression)).(GCLKeyedS);
   gclaction listener interface keyed := gcmap (consid_morphism (scheme.(IParameter) interface) (pgcm_expression program)) ((egraphicalcore program.(pexpression)).(gclaction) listener interface keyed);
|}.
#[local] Instance pgraphicalcore_Finite {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {MInput_Finite: forall method: scheme.(Method), Finite (scheme.(MInput) method)} (program: Program): FiniteGraphicalCore (pgraphicalcore program).
Proof.
  unfold pgraphicalcore.
  unfold PGCAbstract.
  unfold PGCNode.
  unfold PGCConstraint.
  constructor; cbn; apply _.
Qed.

Definition gcmprogram_expression (program: Program): GCMorphism (egraphicalcore program.(pexpression)) (pgraphicalcore program)
:= Build_GCMorphism _ _ (egraphicalcore program.(pexpression)) (pgraphicalcore program)
                    Some
                    (fun listener => listener)
                    inl
                    Some
                    (fun node => eqS_refl _)
                    (fun listener interface keyed => keyed)
                    (fun listener interface keyed => gcmap_morphism _ ((egraphicalcore program.(pexpression)).(gclaction) listener interface keyed)).
Lemma gcmprogram_expressionv {Interface_SSet: SSet scheme.(Interface)} (program: Program): GCMorphismV (core' := pgraphicalcore program) (cons_morphism (fun _ => None) nil_morphism) (gcmprogram_expression program).
Proof.
  constructor; intros.
  + rewrite convert_id.
    reflexivity.
  + reflexivity.
  + reflexivity.
  + apply gcmap_morphismv.
Qed.
Lemma gcmprogram_expressionr {Interface_SSet: SSet scheme.(Interface)} (program: Program): GCReflectsS (core' := pgraphicalcore program) (gcmprogram_expression program).
Proof.
  constructor; cbn; intros.
  + assumption.
  + apply gcmap_morphismr.
Qed.

Lemma pgraphicalcore_sound
      {Interface_SSet: SSet scheme.(Interface)}
      (program: Program)
      (history: GCHistory (pgraphicalcore program))
      (space: TypeSpace)
      (model: Model history space)
    : HierarchyV
   -> ExpressionValidS program.(pexpression)
   -> FinalGCHistory history
   -> ModelV model nil_elimination
   -> CheckExpression space nil_elimination program.(pexpression) (tsubst emptye program.(ptype)).
Proof.
  intros vhierarchy vexpression final vmodel.
  apply cesub with (model.(mabstract) None).
  + set (morphism := gcmprogram_expression program).
    pose proof (gcmprogram_expressionv program) as vmorphism.
    pose proof (gcmprogram_expressionr program) as rmorphism.
    apply egraphicalcore_sound with (gcprehistory morphism history) (compose_model morphism model); try apply final_gcprehistory; try assumption.
    constructor; cbn.
    - intro constraint.
      pose proof (vmodel.(mconstraintv) (Some constraint)) as sub.
      cbn in sub.
      unfold meliminatel in sub.
      rewrite <- apply_eliminate_morphism in sub.
      unfold meliminationl in sub.
      rewrite eliminate_consid_pair_elimination in sub.
      unfold meliminate in sub.
      unfold melimination in sub.
      rewrite <- apply_eliminate_morphism in sub.
      unfold pgcm_expression_node in sub.
      rewrite eliminate_consid_pair_elimination in sub.
      rewrite eliminate_cons_pair_elimination in sub.
      unfold pgcm_expression in sub.
      rewrite eliminate_pair_morphism in sub.
      rewrite eliminate_select_head_pair_elimination in sub.
      rewrite eliminate_pair_morphism in sub.
      rewrite eliminate_select_head_pair_elimination in sub.
      rewrite eliminate_nil_morphism in sub.
      assumption.
    - cbn.
      intro node.
      unfold compose.
      eapply space.(ssttrans); try apply vmodel.(mlowerv).
      apply space.(sstvariance).
      intro parameter.
      unfold meliminate.
      unfold melimination.
      cbn.
      rewrite <- apply_eliminate_morphism.
      unfold pgcm_expression_node.
      rewrite eliminate_consid_pair_elimination.
      rewrite eliminate_cons_pair_elimination.
      apply signed_refl.
      apply space.(sstrefl).
    - cbn.
      intro node.
      unfold compose.
      eapply space.(ssttrans); try apply vmodel.(mupperv).
      apply space.(sstvariance).
      intro parameter.
      unfold meliminate.
      unfold melimination.
      cbn.
      rewrite <- apply_eliminate_morphism.
      unfold pgcm_expression_node.
      rewrite eliminate_consid_pair_elimination.
      rewrite eliminate_cons_pair_elimination.
      apply signed_refl.
      apply space.(sstrefl).
    - intros listener interface [ keyed hkeyed ].
      cbn.
      apply vmodel.(mlargumentv).
    - intros listener interface [ keyed hkeyed ].
      pose proof (compose_modelv (gcmap_morphism (consid_morphism (scheme.(IParameter) interface) (pgcm_expression program)) _) (history.(gchaction) listener interface hkeyed) (model.(mlaction) listener interface hkeyed) (extend_morphism _ (consid_morphism _ (pgcm_expression program))) (pair_elimination (model.(mlargument) _ _ hkeyed) (pair_elimination model.(mabstract) nil_elimination))) as vmodel'.
      rewrite eliminate_extend_morphism_pair_elimination in vmodel'.
      rewrite eliminate_consid_pair_elimination in vmodel'.
      unfold pgcm_expression in vmodel'.
      rewrite eliminate_pair_morphism in vmodel'.
      rewrite eliminate_select_head_pair_elimination in vmodel'.
      rewrite eliminate_pair_morphism in vmodel'.
      rewrite eliminate_select_head_pair_elimination in vmodel'.
      rewrite eliminate_nil_morphism in vmodel'.
      apply vmodel'; try assumption.
      apply gcmap_morphismv.
      apply vmodel.(mlactionv).
    - apply vmodel.(munresolvedv).
  + eapply space.(ssttrans); try apply (vmodel.(mconstraintv) None).
    unfold meliminatel.
    unfold meliminationl.
    unfold melimination.
    simpl.
    rewrite <- apply_eliminate_morphism.
    unfold pgcm_type.
    rewrite eliminate_consid_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_cons_pair_elimination.
    rewrite eliminate_nil_morphism.
    eapply space.(ssttrans); try apply tsubst_closed.
    apply (msubstv_upper model nil_elimination (select_head emptye)) with (einterface := fun parameter => eqS_refl _); try assumption.
    cbn.
    intros location parameter.
    rewrite convert_id.
    reflexivity.
Qed.

Lemma pgraphicalcore_complete
      {Interface_SSet: SSet scheme.(Interface)}
      {MInput_SSet: forall method: scheme.(Method), SSet (scheme.(MInput) method)}
      {MInput_Projective: forall method: scheme.(Method), Projective (scheme.(MInput) method)}
      (program: Program)
      (space: TypeSpace)
    : HierarchyV
   -> CheckExpression space nil_elimination program.(pexpression) (tsubst emptye program.(ptype))
   -> existsTSS history: GCHistory (pgraphicalcore program),
      FinalGCHistory history
    & existsTS model: Model history space,
      ModelV model nil_elimination.
Proof.
  intros vhierarchy check.
  apply egraphicalcore_complete in check; try assumption.
  destruct check as [ history final [ model vmodel ] ].
  pose (Build_GCHistory nil (pgraphicalcore program)
                        history.(GCHKeyedS)
                        history.(GCHUnResolvedS)
                        (fun listener interface hkeyed => history.(gchkeyed) hkeyed)
                        (fun listener interface hkeyed => gcmap_history _ (history.(gchaction) listener interface hkeyed))) as expressionhistory.
  exists expressionhistory.
  + constructor; cbn.
    - apply final.(fgchunique).
    - apply final.(fgchunresolved).
    - apply final.(fgchresolved).
    - intros listener interface hkeyed.
      apply final_gcmap_history.
      apply final.(fgchaction).
  + pose (Build_Model nil (pgraphicalcore program) expressionhistory space
                      (optione (tsubst emptye program.(ptype)) model.(mabstract))
                      model.(mlistener)
                      (sume model.(mnode) (fun location => space.(stinterface) (linterface location) (fun parameter => tsubst emptye (ltargument location parameter))))
                      model.(mlargument)
                      (fun listener interface hkeyed => gcmap_model _ (model.(mlaction) listener interface hkeyed))) as expressionmodel.
    exists expressionmodel.
    constructor; cbn.
    - intros [ constraint | ].
      * unfold meliminatel.
        unfold meliminationl.
        rewrite <- apply_eliminate_morphism.
        rewrite eliminate_consid_pair_elimination.
        unfold meliminate.
        unfold melimination.
        rewrite <- apply_eliminate_morphism.
        cbn.
        rewrite eliminate_extend_selection_pair_elimination.
        rewrite eliminate_extend_selection_pair_elimination.
        rewrite eliminate_extend_selection_pair_elimination.
        rewrite eliminate_extend_selection_pair_elimination.
        rewrite eliminate_extend_selection_pair_elimination.
        rewrite eliminate_select_head_pair_elimination.
        rewrite eliminate_select_head_pair_elimination.
        rewrite eliminate_select_head_pair_elimination.
        rewrite eliminate_select_head_pair_elimination.
        unfold compose.
        simpl.
        apply vmodel.(mconstraintv).
      * unfold meliminatel.
        unfold meliminationl.
        unfold meliminate.
        unfold melimination.
        cbn.
        rewrite <- apply_eliminate_morphism.
        unfold pgcm_type.
        rewrite eliminate_consid_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        rewrite eliminate_nil_morphism.
        unfold compose.
        simpl.
        generalize program.(ptype).
        intro type.
        destruct type as [ [ ] | | ? ? ]; apply space.(sstrefl).
    - intros [ node | location ]; simpl.
      * eapply space.(ssttrans); try apply vmodel.(mlowerv).
        apply space.(sstvariance).
        intro parameter.
        unfold meliminate.
        unfold melimination.
        rewrite <- apply_eliminate_morphism.
        unfold pgcm_expression_node.
        rewrite eliminate_consid_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        unfold pgcm_expression.
        rewrite eliminate_pair_morphism.
        rewrite eliminate_select_head_pair_elimination.
        rewrite eliminate_pair_morphism.
        rewrite eliminate_select_head_pair_elimination.
        rewrite eliminate_nil_morphism.
        apply signed_refl.
        apply space.(sstrefl).
      * apply space.(sstvariance).
        intro parameter.
        unfold meliminate.
        unfold melimination.
        rewrite <- apply_eliminate_morphism.
        unfold pgcm_type.
        rewrite eliminate_consid_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        rewrite eliminate_nil_morphism.
        unfold compose.
        cbn.
        rewrite tsubst_ltargument.
        erewrite space_largument_closed.
        apply signed_refl.
        apply space.(sstrefl).
    - intros [ node | location ]; simpl.
      * eapply space.(ssttrans); try apply vmodel.(mupperv).
        apply space.(sstvariance).
        intro parameter.
        unfold meliminate.
        unfold melimination.
        rewrite <- apply_eliminate_morphism.
        unfold pgcm_expression_node.
        rewrite eliminate_consid_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        unfold pgcm_expression.
        rewrite eliminate_pair_morphism.
        rewrite eliminate_select_head_pair_elimination.
        rewrite eliminate_pair_morphism.
        rewrite eliminate_select_head_pair_elimination.
        rewrite eliminate_nil_morphism.
        apply signed_refl.
        apply space.(sstrefl).
      * apply space.(sstvariance).
        intro parameter.
        unfold meliminate.
        unfold melimination.
        rewrite <- apply_eliminate_morphism.
        unfold pgcm_type.
        rewrite eliminate_consid_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        rewrite eliminate_cons_pair_elimination.
        rewrite eliminate_nil_morphism.
        unfold compose.
        cbn.
        rewrite tsubst_ltargument.
        erewrite space_largument_closed.
        apply signed_refl.
        apply space.(sstrefl).
    - apply vmodel.(mlargumentv).
    - intros listener interface hkeyed.
      apply gcmap_modelv.
      apply vmodel.(mlactionv).
    - apply vmodel.(munresolvedv).
Qed.



(* Part 12: Decidability *)

(* Part 12.1: Decidability of Type Validity
 * Here we prove Lemma 6.1 of the paper: that whether or not a given type has a given variance within a given kind context is decidable.
 *)

#[local] Instance UserVariance_DecidableS {Interface_SSet: SSet scheme.(Interface)} {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {Var: Type} (variance: Var -> Sign) (sign: Sign) (type: UserType Var): DecidableS (UserVariance variance type sign).
Proof.
  revert sign; induction type as [ variable | | interface arguments IHarguments ]; intro sign.
  + destruct (dec_eq (variance variable) sign) as [ e | ne ].
    - left.
      destruct e.
      apply uvvariable.
    - right.
      intro uv.
      inversion uv; subst.
      apply false_falseS.
      apply ne.
      reflexivity.
  + left.
    apply uvany.
  + destruct (finite_splitterS' _ _ (fun parameter => IHarguments parameter (multiply sign ((hierarchy.(hinterface) interface).(uisvariance) parameter)))) as [ variable nuv | uv ].
    - right.
      intro uv.
      inversion_hset uv.
      auto.
    - left.
      apply uvinterface.
      intro parameter.
      apply uv.
Qed.



(* Part 12.2: Decidability of Hierarchy Validity
 * Here we prove Lemma 6.2 of the paper: that whether or not the given hierarchy is valid is decidable.
 *)

#[local] Instance UserMethodSignatureV_DecidableS {Interface_SSet: SSet scheme.(Interface)} {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {Var: Type} (variance: Var -> Sign) {Input: Type} {Input_Finite: Finite Input} (signature: UserMethodSignature Var Input): DecidableS (UserMethodSignatureV signature variance).
Proof.
  destruct (finite_splitterS' _ _ (fun input => UserVariance_DecidableS variance negative (signature.(umsinput) input))) as [ input nuvinput | uvinput ].
  + right.
    intro vsignature.
    apply nuvinput.
    apply vsignature.(umsinputv).
  + destruct (decidableS (UserVariance variance signature.(umsresult) positive)) as [ uvresult | nuvresult ].
    - left.
      constructor; assumption.
    - right.
      intro vsignature.
      apply nuvresult.
      apply vsignature.(umsresultv).
Qed.
#[local] Instance UserBodySignatureV_DecidableS {Interface_SSet: SSet scheme.(Interface)} {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {MInput_Finite: forall method: scheme.(Method), Finite (scheme.(MInput) method)} {Var: Type} (variance: Var -> Sign) (signature: UserBodySignature Var): DecidableS (UserBodySignatureV signature variance).
Proof.
  destruct (scset_splitterS' signature.(ubsmethods) _ _ (fun method contains => UserMethodSignatureV_DecidableS variance (signature.(ubsmethod) method contains))) as [ vmethods | nvmethod ].
  + left.
    constructor.
    assumption.
  + right.
    intro vsignature.
    destruct nvmethod as [ method [ contains nvmethod ] ].
    apply nvmethod.
    apply vsignature.(ubsmethodv).
Qed.
#[local] Instance UserInterfaceSignatureV_DecidableS {Interface_SSet: SSet scheme.(Interface)} {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {MInput_Finite: forall method: scheme.(Method), Finite (scheme.(MInput) method)} {Var: Type} (signature: UserInterfaceSignature Var): DecidableS (UserInterfaceSignatureV signature).
Proof.
  destruct (decidableS (UserBodySignatureV signature.(uisbody) signature.(uisvariance))) as [ vbody | nvbody ].
  + left.
    constructor.
    assumption.
  + right.
    intro vsignature.
    apply nvbody.
    apply vsignature.(uisbodyv).
Qed.
(* Note that this is the key place that requires the set of interfaces to be finite.
 * This is so that we can check that each interface has a valid signature.
 * Thus, if we were to know that many interfaces necessarily had valid signatures, say because they represent "built-in" structural types, we could support an infinite set of interfaces.
 * That is, really only the set of user-defined interfaces needs to be finite.
 *)
#[local] Instance HierarchyV_DecidableS {Interface_Finite: Finite scheme.(Interface)} {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)} {MInput_Finite: forall method: scheme.(Method), Finite (scheme.(MInput) method)}: DecidableS HierarchyV.
Proof.
  destruct (@finite_splitterS' scheme.(Interface) _ _ _ (fun interface => UserInterfaceSignatureV_DecidableS (hierarchy.(hinterface) interface))) as [ interface nvsignature | vsignature ].
  + right.
    intro vhierarchy.
    apply nvsignature.
    apply vhierarchy.(hinterfacev).
  + left.
    constructor.
    assumption.
Qed.



(* Part 12.3: Decidability of Type-Checkability
 * Here we prove Lemma 9.3 of the paper: that whether or not a given expression is type-checkable in the given hierarchy is decidable.
 *)

#[local] Instance ExpressionValidS_DecidableS {MInput_Finite: forall method: scheme.(Method), Finite (scheme.(MInput) method)} {Input: Sort} (expression: Expression Input): DecidableS (ExpressionValidS expression).
Proof.
  induction expression as [ Input input | Input reciever IHreciever method arguments IHarguments | Input interface methods bodies IHbodies ]; simpl.
  + left.
    constructor.
  + destruct IHreciever as [ vreciever | nvreciever ].
    - destruct (finite_splitterS' _ _ IHarguments) as [ parameter nvargument | varguments ].
      * right.
        intros [ _ varguments ].
        apply nvargument.
        apply varguments.
      * left.
        split; assumption.
    - right.
      intros [ vreciever _ ].
      apply nvreciever.
      exact vreciever.
  + destruct (scset_splitterS' _ _ _ (fun method (contains: SCSetContains (hierarchy.(hinterface) interface).(uisbody).(ubsmethods) method) => SCSetContains_DecidableS methods method)) as [ includes | nincludes ].
    - destruct (scset_splitterS' _ _ _ IHbodies) as [ vbodies | nvbodies ].
      * left.
        split; assumption.
      * right.
        destruct nvbodies as [ method [ contains nvbody ] ].
        intros [ _ vbodies ].
        apply nvbody.
        apply vbodies.
    - right.
      destruct nincludes as [ method [ contains nincludes ] ].
      intros [ includes _ ].
      apply nincludes.
      apply includes.
      exact contains.
Qed.



(* Part 12.4: Decidability of Type-Consistent Program Validity
 * Here we prove Theorem 9.7 of the paper: that whether or not a given program is valid according to type-consistency is decidable.
 *)
Theorem programv_decider
      {Interface_Finite: Finite scheme.(Interface)}
      {IParameter_Finite: forall interface: scheme.(Interface), Finite (scheme.(IParameter) interface)}
      {MInput_Finite: forall method: scheme.(Method), Finite (scheme.(MInput) method)}
      (program: Program)
    : DeciderS (ProgramV program).
Proof.
  destruct (decidableS HierarchyV) as [ vhierarchy | nvhierarchy ].
  + destruct (decidableS (ExpressionValidS program.(pexpression))) as [ vexpression | nvexpression ].
    - pose (pgraphicalcore program) as core.
      destruct (decidableS (existsTS history: GCHistory core, AndS (FinalGCHistory history) (ConsistentGC history))) as [ consistent | nconsistent ].
      * left.
        destruct consistent as [ history [ final consistent ] ].
        constructor; try assumption.
        eexists; try (eapply consistent_gc_ts; eassumption).
        eapply pgraphicalcore_sound with (model := gctsmodel history); try eassumption.
        apply (gctsmodelv history).
      * right.
        intro vprogram.
        apply nconsistent.
        destruct vprogram.(pexpressionv) as [ space consistent check ].
        apply pgraphicalcore_complete in check; try assumption.
        destruct check as [ history final [ model vmodel ] ].
        exists history.
        split; try assumption.
        eapply consistent_ts_gc; eassumption.
    - right.
      intro vprogram.
      apply pexpressionv in vprogram.
      destruct vprogram as [ space _ check ].
      apply check_valid in check.
      auto.
  + right.
    intro vprogram.
    apply nvhierarchy.
    apply vprogram.(phierarchyv).
Qed.

(* The following prints only scheme: Scheme and hierarchy: Hierarchy. *)
Print Assumptions programv_decider.
