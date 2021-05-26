(** Heaps and heap assertions for separation logics. *)

From Coq Require Import ssreflect ssrbool Lia FunctionalExtensionality PropExtensionality.
From mathcomp Require Import ssrint ssrnum ssralg eqtype order zify.
Import Order.Theory.
Local Open Scope ring_scope.

(*From Coq Require Import ZArith Lia Bool String List.
From Coq Require Import FunctionalExtensionality PropExtensionality.
Local Open Scope Z_scope.*)

(** * 1. Memory heaps *)

(** A memory heap is a partial function from addresses (memory locations)
    to values, with a finite domain. *)

Definition addr := int.

Record heap : Type := {
  contents :> addr -> option int;
  isfinite :  exists i, forall j, i <= j -> contents j = None
}.

Lemma heap_extensionality:
  forall (h1 h2: heap),
  (forall l, h1 l = h2 l) -> h1 = h2.
Proof.
move=>[c1 F1][c2 F2] H.
have E : c1 = c2 by apply/functional_extensionality/H.
rewrite E in F1 H *.
suff : F1 = F2 by move=>->.
by apply: proof_irrelevance.
Qed.

(** The empty heap. *)

Program Definition hempty : heap :=
  {| contents := fun l => None |}.
Next Obligation.
by exists 0.
Qed.

(** The heap that contains [v] at address [l] and is equal to [h] on
    all other addresses. *)

Program Definition hupdate (l: addr) (v: int) (h: heap) : heap :=
  {| contents := fun m => if l == m then Some v else h m |}.
Next Obligation.
case: (isfinite h)=>[i Fi].
exists (Order.max i (l+1))=>j H.
case/boolP: (_ == _); first by lia.
by move=>_; apply: Fi; lia.
Qed.

Lemma hupdate_same: forall l v h, (hupdate l v h) l = Some v.
Proof.
by move=>??? /=; rewrite eq_refl.
Qed.

Lemma hupdate_other: forall l v h l', l <> l' -> (hupdate l v h) l' = h l'.
Proof.
by move=>???? /=; case: eqP.
Qed.

(** The heap [h] after deallocating address [l]. *)

Program Definition hfree (l: addr) (h: heap) : heap :=
  {| contents := fun l' => if l == l' then None else h l' |}.
Next Obligation.
case: (isfinite h)=>[i Fi].
exists i=>??; case: ifP=>// _.
by apply: Fi.
Qed.

(** The heap [h] where addresses [l, ..., l + sz - 1] are initialized to 0. *)

Fixpoint hinit (l: addr) (sz: nat) (h: heap) : heap :=
  match sz with O => h | S sz => hupdate l 0 (hinit (l + 1) sz h) end.

Lemma hinit_inside:
  forall h (sz :nat) l l', l <= l' < l + Posz sz -> hinit l sz h l' = Some 0.
Proof.
move=>?; elim=>/=.
- by lia.
- move=>? IH ???; case: ifP=>// ?.
  by apply: IH; lia.
Qed.

Lemma hinit_outside:
  forall h sz l l', l' < l \/ l + Posz sz <= l' -> hinit l sz h l' = h l'.
Proof.
move=>?; elim=>//=.
move=>? IH ???; case: ifP.
- by lia.
- by move=>?; apply: IH; lia.
Qed.

(** The disjoint union of two heaps. *)

Definition hdisjoint (h1 h2: heap) : Prop :=
  forall l, h1 l = None \/ h2 l = None.

Lemma hdisjoint_sym:
  forall h1 h2, hdisjoint h1 h2 <-> hdisjoint h2 h1.
Proof.
by rewrite /hdisjoint=>??; split=>H l; case: (H l); try by [left|right].
Qed.

Program Definition hunion (h1 h2: heap) : heap :=
  {| contents := fun l => if h1 l then h1 l else h2 l |}.
Next Obligation.
case: (isfinite h1)=>[i1 F1].
case: (isfinite h2)=>[i2 F2].
exists (Order.max i1 i2)=>??.
by rewrite F1 ?F2=>//; lia.
Qed.

Lemma hunion_comm:
  forall h1 h2, hdisjoint h1 h2 -> hunion h2 h1 = hunion h1 h2.
Proof.
move=>h1 h2 H; apply: heap_extensionality=>l /=.
by case: (H l)=>->/=; [case: (h2 l)| case: (h1 l)].
Qed.

Lemma hunion_assoc:
  forall h1 h2 h3, hunion (hunion h1 h2) h3 = hunion h1 (hunion h2 h3).
Proof.
move=>h1 ??; apply: heap_extensionality=>l /=.
by case: (h1 l).
Qed.

Lemma hunion_empty:
  forall h, hunion hempty h = h.
Proof.
by move=>?; apply: heap_extensionality.
Qed.

Lemma hdisjoint_empty:
  forall h, hdisjoint h h -> h = hempty.
Proof.
move=>? H; apply: heap_extensionality=>l.
by case: (H l)=>->.
Qed.

Lemma hdisjoint_union_l:
  forall h1 h2 h3,
  hdisjoint (hunion h1 h2) h3 <-> hdisjoint h1 h3 /\ hdisjoint h2 h3.
Proof.
rewrite /hdisjoint /hunion /= => h1 ??; split.
- by move=>H; split=>l; case: (H l); try by [right]; case: (h1 l)=>//= ?; left.
- move=>[H1 H2] l; case: (H2 l)=>->; case E: (h1 l)=>/=; [right|left|right|right]=>//.
  by case: (H1 l)=>//; rewrite E.
Qed.

Lemma hdisjoint_union_r:
  forall h1 h2 h3,
  hdisjoint h1 (hunion h2 h3) <-> hdisjoint h1 h2 /\ hdisjoint h1 h3.
Proof.
move=>? h2 h3.
by rewrite hdisjoint_sym hdisjoint_union_l (hdisjoint_sym h2) (hdisjoint_sym h3).
Qed.

(** Disjointness between three heaps. *)

Definition hdisj3 (h1 h2 h3: heap) :=
  hdisjoint h1 h2 /\ hdisjoint h1 h3 /\ hdisjoint h2 h3.

(** A tactic to prove disjointness statements. *)

(*
Ltac HDISJ :=
  match goal with
  | [ H: hdisj3 _ _ _ |- _ ] =>
      destruct H as (? & ? & ?); HDISJ
  | [ H: hdisjoint (hunion _ _) _ |- _ ] =>
      apply hdisjoint_union_l in H; destruct H; HDISJ
  | [ H: hdisjoint _ (hunion _ _) |- _ ] =>
      apply hdisjoint_union_r in H; destruct H; HDISJ
  | [ |- hdisj3 _ _ _ ] =>
      split; [|split]; HDISJ
  | [ |- hdisjoint (hunion _ _) _ ] =>
      apply hdisjoint_union_l; split; HDISJ
  | [ |- hdisjoint _ (hunion _ _) ] =>
      apply hdisjoint_union_r; split; HDISJ
  | [ |- hdisjoint hempty _ ] =>
      red; auto
  | [ |- hdisjoint _ hempty ] =>
      red; auto
  | [ |- hdisjoint _ _ ] =>
      assumption || (apply hdisjoint_sym; assumption) || idtac
  | _ => idtac
  end.
*)
Lemma hunion_invert_r:
  forall h1 h2 h,
  hunion h h1 = hunion h h2 -> hdisjoint h h1 -> hdisjoint h h2 -> h1 = h2.
Proof.
move=>h1 h2 h H H1 H2; apply: heap_extensionality=>l.
have /= Hl : hunion h h1 l = hunion h h2 l by rewrite H.
by case: (H1 l); case: (H2 l); move: Hl; case: (h l)=>// ??->->.
Qed.

Lemma hunion_invert_l:
  forall h1 h2 h,
  hunion h1 h = hunion h2 h -> hdisjoint h1 h -> hdisjoint h2 h -> h1 = h2.
Proof.
move=>? h2  h ???; apply: (hunion_invert_r _ _ h).
- by rewrite hunion_comm // [in RHS]hunion_comm.
- by rewrite hdisjoint_sym.
- by rewrite hdisjoint_sym.
Qed.

(** * 2. Assertions for separation logic *)

Definition assertion : Type := heap -> Prop.

(** Implication (entailment). *)

Definition aimp (P Q: assertion) : Prop :=
  forall h, P h -> Q h.

Notation "P -->> Q" := (aimp P Q) (at level 95, no associativity).

(** Quantification. *)

Definition aexists {A: Type} (P: A -> assertion) : assertion :=
  fun h => exists a: A, P a h.

Definition aforall {A: Type} (P: A -> assertion) : assertion :=
  fun h => forall a: A, P a h.

(** The assertion "the heap is empty". *)

Definition emp : assertion :=
  fun h => h = hempty.

(** The pure assertion: "the heap is empty and P holds". *)

Definition pure (P: Prop) : assertion :=
  fun h => P /\ h = hempty.

(** The assertion "address [l] contains value [v]".
    The domain of the heap must be the singleton [{l}]. *)

Definition contains (l: addr) (v: int) : assertion :=
  fun h => h = hupdate l v hempty.

(** The assertion "address [l] is valid" (i.e. in the domain of the heap). *)

Definition valid (l: addr) : assertion := aexists (contains l).

(** The separating conjunction. *)

Definition sepconj (P Q: assertion) : assertion :=
  fun h => exists h1 h2, P h1
                      /\ Q h2
                      /\ hdisjoint h1 h2  /\ h = hunion h1 h2.

Notation "P ** Q" := (sepconj P Q) (at level 60, right associativity).

(** The conjunction of a simple assertion and a general assertion. *)

Definition pureconj (P: Prop) (Q: assertion) : assertion :=
  fun h => P /\ Q h.

Notation "P //\\ Q" := (pureconj P Q) (at level 60, right associativity).

(** Plain conjunction and disjunction. *)

Definition aand (P Q: assertion) : assertion :=
  fun h => P h /\ Q h.
Definition aor (P Q: assertion) : assertion :=
  fun h => P h \/ Q h.

(** Extensional equality between assertions. *)

Lemma assertion_extensionality:
  forall (P Q: assertion),
  (forall h, P h <-> Q h) -> P = Q.
Proof.
move=>?? H; apply: functional_extensionality=>?.
by apply/propositional_extensionality/H.
Qed.

(** ** Properties of separating conjunction *)

Lemma sepconj_comm: forall P Q, P ** Q = Q ** P.
Proof.
have E : forall P Q h, (P ** Q) h -> (Q ** P) h.
- move=>???[h1][h2][?][?][D]->.
  have Ds : hdisjoint h2 h1 by rewrite hdisjoint_sym.
  exists h2, h1; do!split=>//.
  by rewrite hunion_comm.
by move=>??; apply: assertion_extensionality=>?; split; apply: E.
Qed.

Lemma sepconj_assoc: forall P Q R, (P ** Q) ** R = P ** (Q ** R).
Proof.
move=>???; apply: assertion_extensionality=>?; split.
- move=>[?][h1][[h2][h3][?][?][?]->][?][D]->.
  rewrite hunion_assoc.
  move: D; rewrite hdisjoint_union_l; case=>??.
  by exists h2, (hunion h3 h1); do!split=>//; [exists h3, h1|rewrite hdisjoint_union_r].
move=>[h1][?][?][[h2][h3][?][?][?]->][D]->.
rewrite -hunion_assoc.
move: D; rewrite hdisjoint_union_r; case=>??.
by exists (hunion h1 h2), h3; do!split=>//; [exists h1, h2|rewrite hdisjoint_union_l].
Qed.

Lemma sepconj_emp: forall P, emp ** P = P.
Proof.
move=>?; apply: assertion_extensionality=>h; split.
- move=>[?][?][HE][?][?]->; rewrite /emp in HE.
  by rewrite HE hunion_empty.
- by move=>?; exists hempty, h; do!split=>//; [move=>?; left | rewrite hunion_empty].
Qed.

Lemma sepconj_imp_l: forall P Q R,
  (P -->> Q) -> (P ** R -->> Q ** R).
Proof.
move=>??? H ?[h1][h2][?][?][?]->.
exists h1, h2; do!split=>//.
by apply: H.
Qed.

Lemma sepconj_imp_r: forall P Q R,
  (P -->> Q) -> (R ** P -->> R ** Q).
Proof.
move=>?? R ??.
rewrite 2!(sepconj_comm R).
by apply: sepconj_imp_l.
Qed.

(** ** Other useful logical properties *)

Lemma pure_sep: forall P Q,
  pure (P /\ Q) = pure P ** pure Q.
Proof.
move=>??; apply: assertion_extensionality=>?.
rewrite /pure /sepconj; split.
- by move=>[[??]]->; exists hempty, hempty; do!split=>//; [left | rewrite hunion_empty].
- move=>[?][?][[? ->]][[? ->]][_]->; do!split=>//.
  by rewrite hunion_empty.
Qed.

Lemma pureconj_sepconj: forall P Q,
  pure P ** Q = P //\\ Q.
Proof.
move=>??; apply: assertion_extensionality=>h.
rewrite /pure /sepconj /pureconj; split.
- move=>[?][?][[? ->]][?][?]->.
  by rewrite hunion_empty.
- by move=>[??]; exists hempty, h; do!split=>//; [left | rewrite hunion_empty].
Qed.

Lemma lift_pureconj: forall P Q R, (P //\\ Q) ** R = P //\\ (Q ** R).
Proof.
by move=>???; rewrite -2!pureconj_sepconj sepconj_assoc.
Qed.

Lemma lift_aexists: forall (A: Type) (P: A -> assertion) Q,
  aexists P ** Q = aexists (fun x => P x ** Q).
Proof.
move=>???; apply: assertion_extensionality=>?; split.
- move=>[h1][h2][[a ?]][?][?]->.
  by exists a,h1,h2.
- move=>[a][h1][h2][?][?][?]->.
  exists h1,h2; do!split=>//.
  by exists a.
Qed.

Lemma sepconj_swap3: forall R P Q, P ** Q ** R = R ** P ** Q.
Proof.
by move=>???; rewrite -sepconj_assoc sepconj_comm.
Qed.

Lemma sepconj_swap4: forall S P Q R, P ** Q ** R ** S = S ** P ** Q ** R.
Proof.
by move=>????; rewrite -sepconj_assoc sepconj_swap3 sepconj_assoc.
Qed.

Lemma sepconj_pick2: forall Q P R, P ** Q ** R = Q ** P ** R.
Proof.
by move=>Q ??; rewrite (sepconj_comm Q) -sepconj_assoc sepconj_comm.
Qed.

Lemma sepconj_pick3: forall R P Q S, P ** Q ** R ** S = R ** P ** Q ** S.
Proof.
by move=>R P ??; rewrite (sepconj_pick2 R) (sepconj_pick2 P).
Qed.

(** ** Magic wand *)

Definition wand (P Q: assertion) : assertion :=
  fun h => forall h', hdisjoint h h' -> P h' -> Q (hunion h h').

Notation "P --* Q" := (wand P Q) (at level 70, right associativity).

Lemma wand_intro: forall P Q R,
  P ** Q -->> R  ->  P -->> Q --* R.
Proof.
move=>??? I h1 ? h2 ??.
by apply: I; exists h1,h2.
Qed.

Lemma wand_cancel: forall P Q,
  P ** (P --* Q) -->> Q.
Proof.
move=>???[h1][h2][?][WH][?]->.
have D: hdisjoint h2 h1 by rewrite hdisjoint_sym.
rewrite hunion_comm //.
by apply: WH.
Qed.

Lemma wand_charact: forall P Q,
  (P --*Q) = (aexists (fun R => (P ** R -->> Q) //\\ R)).
Proof.
move=>P Q; apply assertion_extensionality=>h; split.
- move=>?; exists (P --* Q); split=>//.
  by apply: wand_cancel.
- move=>[?][A]? h1 ??.
  have D: hdisjoint h1 h by rewrite hdisjoint_sym.
  rewrite hunion_comm //.
  by apply: A; exists h1,h.
Qed.

Lemma wand_equiv: forall P Q R,
  (P -->> (Q --* R)) <-> (P ** Q -->> R).
Proof.
move=>???; split=>H.
- move=>?[?][?][?][?][?]->.
  by apply: H.
- by apply: wand_intro.
Qed.

Lemma wand_imp_l: forall P P' Q,
  (P' -->> P) -> (P --* Q -->> P' --* Q).
Proof.
by move=>??? H ? W ???; apply/W/H.
Qed.

Lemma wand_imp_r: forall P Q Q',
  (Q -->> Q') -> (P --* Q -->> P --* Q').
Proof.
by move=>??? H ? W ???; apply/H/W.
Qed.

Lemma wand_idem: forall P,
  emp -->> P --* P.
Proof.
by move=>?? -> ???; rewrite hunion_empty.
Qed.

Lemma wand_pure_l: forall (P: Prop) Q,
  P -> (pure P --* Q) = Q.
Proof.
move=>???; apply assertion_extensionality=>h; split.
- have HE: hdisjoint h hempty by right.
  move=>W; rewrite -(hunion_empty h) hunion_comm //.
  by apply: W.
- move=>???[?->]; rewrite hunion_comm; last by left.
  by rewrite hunion_empty.
Qed.

Lemma wand_curry: forall P Q R,
  (P ** Q --* R) = (P --* Q --* R).
Proof.
move=>???; apply assertion_extensionality=>?; split.
- move=>W h1 ?? h2; rewrite hdisjoint_union_l; case=>???.
  rewrite hunion_assoc; apply: W; last by exists h1, h2.
  rewrite hunion_comm; last by rewrite hdisjoint_sym.
  by rewrite hdisjoint_union_r.
move=>W ? H[?][?][?][?][?]E.
rewrite {}E in H *; move: H; rewrite hdisjoint_union_r; case=>??.
rewrite -hunion_assoc; apply: W=>//.
by rewrite hdisjoint_union_l.
Qed.

Lemma wand_star: forall P Q R,
  ((P --* Q) ** R ) -->> (P --* (Q ** R)).
Proof.
move=>????[h1][h2][W][?][?]-> h3; rewrite hdisjoint_union_l; case=>???.
exists (hunion h1 h3),h2; do!split=>//.
- by apply: W.
- rewrite hdisjoint_union_l; split=>//.
  by rewrite hdisjoint_sym.
by rewrite !hunion_assoc (hunion_comm h3) // hdisjoint_sym.
Qed.

(** ** Precise assertions *)

(** An assertion is precise if "it unambiguously carves out an area of the heap"
   (in the words of Gotsman, Berdine, Cook, 2011). *)

Definition precise (P: assertion) : Prop :=
  forall h1 h2 h1' h2',
  hdisjoint h1 h2 -> hdisjoint h1' h2' -> hunion h1 h2 = hunion h1' h2' ->
  P h1 -> P h1' -> h1 = h1'.

(** A parameterized assertion is precise if, in addition, the parameter
   is uniquely determined as well. *)

Definition param_precise {X: Type} (P: X -> assertion) : Prop :=
  forall x1 x2 h1 h2 h1' h2',
  hdisjoint h1 h2 -> hdisjoint h1' h2' -> hunion h1 h2 = hunion h1' h2' ->
  P x1 h1 -> P x2 h1' -> x1 = x2 /\ h1 = h1'.

Remark param_precise_precise:
  forall (X: Type) (P: X -> assertion),
  param_precise P -> forall x, precise (P x).
Proof.
move=>?? H x h1 h2 h1' h2' ?????.
by case: (H x x h1 h2 h1' h2').
Qed.

Remark precise_param_precise:
  forall P, precise P -> param_precise (fun _ : unit => P).
Proof.
move=>? H [] [] ?????????; split=>//.
by apply: H.
Qed.

Lemma pure_precise: forall P,
  precise (pure P).
Proof.
by move=>????????[?->][?->].
Qed.

Lemma pure_param_precise: forall (X: Type) (P: X -> Prop),
  (forall x1 x2, P x1 -> P x2 -> x1 = x2) ->
  param_precise (fun x => pure (P x)).
Proof.
move=>?? H ?????????[?->][?->]; split=>//.
by apply: H.
Qed.

Lemma contains_param_precise: forall l,
  param_precise (fun v => contains l v).
Proof.
rewrite /contains=>l ?? h1 h2 h1' h2' H1 H2 HD E1 E2.
have /= E: hunion h1 h2 l = hunion h1' h2' l by rewrite HD.
by rewrite E1 E2 !hupdate_same /= in E *; case: E=>->.
Qed.

Lemma contains_precise: forall l v,
  precise (contains l v).
Proof.
move=>l v ?????????.
apply: (param_precise_precise _ (contains l) _ v)=>//.
by exact: contains_param_precise.
Qed.

Lemma aexists_precise: forall (X: Type) (P: X -> assertion),
  param_precise P -> precise (aexists P).
Proof.
move=>?? H h1 h2 h1' h2' ???[x1 ?][x2 ?].
by case: (H x1 x2 h1 h2 h1' h2').
Qed.

Lemma valid_precise: forall l,
  precise (valid l).
Proof.
move=>l ? h2 ? h2' ?????.
apply: (aexists_precise _ (contains l) _ _ h2 _ h2')=>//.
by exact: contains_param_precise.
Qed.

Lemma sepconj_param_precise: forall (X: Type) (P Q: X -> assertion),
  param_precise P -> (forall x, precise (Q x)) ->
  param_precise (fun x => P x ** Q x).
Proof.
move=>??? H H0 x1 x2 ? h2 ? h2' HD1 HD2 H12 [h3][h4][?][?][?] E1 [h5][h6][?][?][?] E2.
rewrite {}E1 {}E2 in HD1 HD2 H12 *.
case: (H x1 x2 h3 (hunion h4 h2) h5 (hunion h6 h2'))=>//.
- by move: HD1; rewrite hdisjoint_union_r hdisjoint_union_l; case.
- by move: HD2; rewrite hdisjoint_union_r hdisjoint_union_l; case.
- by rewrite -!hunion_assoc.
move=>EX ->; split=>//.
rewrite (H0 x1 h4 (hunion h3 h2) h6 (hunion h5 h2')) //.
- move: HD1; rewrite hdisjoint_union_r hdisjoint_union_l; case=>_; split=>//.
  by rewrite hdisjoint_sym.
- move: HD2; rewrite hdisjoint_union_r hdisjoint_union_l; case=>_; split=>//.
  by rewrite hdisjoint_sym.
- by rewrite -!hunion_assoc (hunion_comm h3) // (hunion_comm h5).
by rewrite EX.
Qed.

Lemma sepconj_precise: forall P Q,
  precise P -> precise Q -> precise (P ** Q).
Proof.
move=>P Q ???????????.
have HP: param_precise (fun _ : unit => P ** Q)
 by apply: sepconj_param_precise=>//; apply precise_param_precise.
by move/param_precise_precise: HP; apply.
Qed.

(** Distributivity laws for precise assertions. *)

Lemma sepconj_and_distr_1: forall P1 P2 Q,
  aand P1 P2 ** Q -->> aand (P1 ** Q) (P2 ** Q).
Proof.
by move=>????[h1][h2][[? ?]][?][?]->; split; exists h1, h2.
Qed.

Lemma sepconj_and_distr_2: forall P1 P2 Q,
  precise Q ->
  aand (P1 ** Q) (P2 ** Q) -->> aand P1 P2 ** Q.
Proof.
move=>P1 P2 ? PQ.
rewrite (sepconj_comm P1) (sepconj_comm P2)=>?[[h1][h2][?][?][?]E1][h3][h4][?][?][?]E2.
have E3: h1 = h3.
- apply: (PQ _ h2 _ h4)=>//.
  by rewrite -E1 -E2.
have E4: h2 = h4.
- apply: (hunion_invert_r _ _ h1)=>//.
  - by rewrite -E1 E3 -E2.
  by rewrite E3.
exists h2, h1; do!split=>//.
- by rewrite E4.
- by rewrite hdisjoint_sym.
- by rewrite hunion_comm.
Qed.

(** Self-conjunction law for precise assertions. *)

Lemma sepconj_self: forall P,
  precise P ->
  P ** P -->> P.
Proof.
move=>? H ?[h1][h2][?][?][?]->.
have D: hdisjoint h2 h1 by rewrite hdisjoint_sym.
have E1: h1 = h2.
- apply: (H _ h2 _ h1)=>//.
  by rewrite hunion_comm.
rewrite -E1 in D; move/hdisjoint_empty: D=>->.
by rewrite hunion_empty.
Qed.
