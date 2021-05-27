(** Separation logic. *)

From Coq Require Import ssreflect ssrfun ssrbool Lia FunctionalExtensionality PropExtensionality.
From mathcomp Require Import ssrint ssrnum ssralg seq eqtype order zify.
From CDF Require Import Sequences Separation.
Import Order.Theory.
Import GRing.Theory.
Local Open Scope ring_scope.

(*
From Coq Require Import ZArith Lia Bool List Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From CDF Require Import Sequences Separation.

Local Open Scope Z_scope.
*)

(** * 1. A language of pointers *)

(** We now define a small programming language to work with pointers to
    mutable state.  The language has variables, but these variables are
    immutable.  This in unlike IMP but like ML: mutable variables are
    expressed as immutable pointers (references) to mutable state. *)

(** As in ML too, we blur the distinction between expressions and commands.
    Every command returns a value, which we take to be an integer,
    in addition to possibly performing effects. *)

(** We use higher-order abstract syntax to represent commands in this
    language.  With first-order abstract syntax, a "let" binding
    [let x = a in b] would be represented using the constructor
<<
    LET: forall (x: ident) (a b: com), com
>>
    With higher-order syntax, we use a Coq function [fun x => b] to
    represent the binding of [x] inside [b]:
<<
    LET: forall (a: com) (b: Z -> com), com
>>
    As a benefit, we can use any Coq expression of type [Z] as a
    pure command of the language, making it unnecessary to define
    syntax and semantics for a specific expression language.
*)

CoInductive com: Type :=
  | PURE (x: int)                       (**r command without effects *)
  | LET (c: com) (f: int -> com)        (**r sequencing of commands *)
  | IFTHENELSE (b: int) (c1 c2: com)    (**r conditional *)
  | ALLOC (sz: nat)                     (**r allocate [sz] words of storage *)
  | GET (l: addr)                       (**r dereference a pointer *)
  | SET (l: addr) (v: int)              (**r assign through a pointer *)
  | FREE (l: addr)                      (**r free one word of storage *)
  | PICK (n: int).                      (**r pick a number between 0 and [n] *)

Definition not_pure (c : com) :=
  match c with PURE _ => false | _ => true end.

(** Some derived forms. *)

Definition SKIP: com := PURE 0.

Definition SEQ (c1 c2: com) := LET c1 (fun _ =>
                               c2).

Definition EITHER (c1 c2: com) := LET (PICK 2) (fun n =>
                                  IFTHENELSE n c1 c2).

(** Reduction semantics. *)

Inductive red: com * heap -> com * heap -> Prop :=
  | red_pick: forall n i h,
      0 <= i < n ->
      red (PICK n, h) (PURE i, h)
  | red_let_done: forall x f h,
      red (LET (PURE x) f, h) (f x, h)
  | red_let_step: forall c f h c' h',
      red (c, h) (c', h') ->
      red (LET c f, h) (LET c' f, h')
  | red_ifthenelse: forall b c1 c2 h,
      red (IFTHENELSE b c1 c2, h) (if b == 0 then c2 else c1, h)
  | red_alloc: forall sz (h: heap) l,
      (forall i, l <= i < l + sz%:Z -> h i = None) ->
      l <> 0 ->
      red (ALLOC sz, h) (PURE l, hinit l sz h)
  | red_get: forall l (h: heap) v,
      h l = Some v ->
      red (GET l, h) (PURE v, h)
  | red_set: forall l v (h: heap),
      h l <> None ->
      red (SET l v, h) (SKIP, hupdate l v h)
  | red_free: forall l (h: heap),
      h l <> None ->
      red (FREE l, h) (SKIP, hfree l h).

(** Absence of run-time errors. [immsafe c h] holds if [c / h] is not
    going to abort immediately on a run-time error, such as dereferencing
    an invalid pointer. *)

Inductive immsafe: com * heap -> Prop :=
  | immsafe_pure: forall v h,
      immsafe (PURE v, h)
  | immsafe_let: forall c f h,
      immsafe (c, h) -> immsafe (LET c f, h)
  | immsafe_ifthenelse: forall b c1 c2 h,
      immsafe (IFTHENELSE b c1 c2, h)
  | immsafe_alloc: forall (sz : nat) (h: heap) l,
      l <> 0 -> (forall i, l <= i < l + sz%:Z -> h i = None) ->
      immsafe (ALLOC sz, h)
  | immsafe_get: forall l (h: heap),
      h l <> None -> immsafe (GET l, h)
  | immsafe_set: forall l v (h: heap),
      h l <> None -> immsafe (SET l v, h)
  | immsafe_free: forall l (h: heap),
      h l <> None -> immsafe (FREE l, h)
  | immsafe_pick: forall n h,
      immsafe (PICK n, h).

(** * 2.  The rules of separation logic *)

Definition precond := assertion.
Definition postcond := int -> assertion.

(** ** 2.1.  Semantic definition of strong triples *)

(** Instead of axiomatizing the rules of separation logic, then prove
    their soundness against the operational semantics, we define
    triples [ ⦃ P ⦄ c ⦃ Q ⦄ ] directly in terms of the
    operational semantics, then show the rules of separation logic as
    lemmas about these semantic triples.

    Note: the way triples are defined below, they are strong triples
    that guarantee termination.  However, we write them with braces
    instead of brackets, for consistency with the third lecture
    and with the literature on separation logic.
 *)

(** [safe c h Q] holds if [c] started in [h] always terminates without errors,
    and when it terminates with value [v], the postcondition [Q v] holds
    of the final heap. *)

Inductive safe: com -> heap -> postcond -> Prop :=
  | safe_done: forall v h (Q: postcond),
      Q v h ->
      safe (PURE v) h Q
  | safe_step: forall c h Q,
      not_pure c ->
      immsafe (c, h) ->
      (forall c' h', red (c, h) (c', h') -> safe c' h' Q) ->
      safe c h Q.

(** We define semantic triples like we did for Hoare logic: *)

Definition triple (P: precond) (c: com) (Q: postcond) :=
  forall h, P h -> safe c h Q.

Notation "⦃ P ⦄ c ⦃ Q ⦄" := (triple P c Q) (at level 90, c at next level).

(** ** 2.2. The frame rule *)

(** The frame rule is valid because the operational semantics has nice
    properties with respect to heap extension: if a command is safe
    in a small heap, it is safe in a bigger heap, and any reduction
    from the bigger heap is simulated by a reduction from the smaller heap. *)

(* generalizing the following two seems a bit too tedious, so I fall back to depind *)

From Coq Require Import Program.Equality.

Lemma immsafe_frame: forall h' c h,
  immsafe (c, h) -> hdisjoint h h' -> immsafe (c, hunion h h').
Proof.
move=>h' ? h H; dependent induction H=>?.
- by exact: immsafe_pure.
- by apply/immsafe_let/IHimmsafe.
- by exact: immsafe_ifthenelse.
- case: (isfinite (hunion h h')) => [m Fm].
  apply: (immsafe_alloc _ _ (Num.max 1 m)); first by lia.
  by move=>??; apply: Fm; lia.
- by apply: immsafe_get=>/=; case E: (h l).
- by apply: immsafe_set=>/=; case E: (h l).
- by apply: immsafe_free=>/=; case E: (h l).
- by exact: immsafe_pick.
Qed.

Lemma red_frame: forall h2 c h1 c' h',
  red (c, hunion h1 h2) (c', h') ->
  immsafe (c, h1) ->
  hdisjoint h1 h2 ->
  exists h1', red (c, h1) (c', h1') /\ hdisjoint h1' h2 /\ h' = hunion h1' h2.
Proof.
move=>h2 ? h1 ? h' R; dependent induction R => I HD.
- case: {-2}_ / I (erefl (PICK n, h1))=>// ??; case=>->->.
  by exists h1; do!split=>//; exact: red_pick.
- case: {-2}_ / I (erefl (LET (PURE x) f, h1))=>// ??? I; case=>EC -> EH; rewrite {}EC {}EH in I *.
  by exists h1; do!split=>//; exact: red_let_done.
- case: {-2}_ / I (erefl (LET c f, h1))=>// c0 ?? I; case=>EC -> EH; rewrite {}EC {}EH in I IHR *.
  case: (IHR h2 c h1 c' h')=>// h3[?][?]?.
  by exists h3; do!split=>//; apply: red_let_step.
- by exists h1; do!split=>//; exact: red_ifthenelse.
- exists (hinit l sz h1); do!split.
  - by apply: red_alloc=>// i LE; move: (H i LE) => /=; case: (h1 i).
  - move=>i.
    have E: l <= i < l + sz%Z \/ (i < l \/ l + sz%Z <= i) by lia.
    case: E.
    - by move=>E; right; move: (H i E)=>/=; case: (h1 i).
    - by move=>?; rewrite hinit_outside.
  apply: heap_extensionality=>i /=.
  have E: l <= i < l + sz%Z \/ (i < l \/ l + sz%Z <= i) by lia.
  case: E=>?.
  - by rewrite !hinit_inside.
  - by rewrite !hinit_outside.
- case: {-2}_ / I (erefl (GET l, h1))=>// ?? EQ; case=>EL EH; rewrite {}EL {}EH in EQ *.
  exists h1; do!split=>//; apply: red_get.
  by move: H=>/=; case E: (h1 l).
- case: {-2}_ / I (erefl (SET l v, h1))=>// ??? EQ; case=>EL -> EH; rewrite {}EL {}EH in EQ *.
  exists (hupdate l v h1); do!split.
  - by apply: red_set.
  - move=>i; move: (HD i)=>/=; case=>?; try by right.
    case: eqP; try by left.
    by move=>E; rewrite E in EQ.
  apply: heap_extensionality=>i /=.
  by case: eqP.
- case: {-2}_ / I (erefl (FREE l, h1))=>// ?? EQ; case=>EL EH; rewrite {}EL {}EH in EQ *.
  exists (hfree l h1); do!split.
  - by apply: red_free.
  - move=>i; move: (HD i)=>/=; case=>?; [left| right]=>//.
    by case: eqP.
  apply: heap_extensionality=>i /=.
  case: eqP=>//= <-.
  by case: (HD l).
Qed.

Lemma safe_frame:
  forall (R: assertion) h', R h' ->
  forall c h Q,
  safe c h Q -> hdisjoint h h' -> safe c (hunion h h') (fun v => Q v ** R).
Proof.
move=>? h' ????; elim.
- move=>? h1 ???; apply: safe_done.
  by exists h1, h'.
- move=>?????? H3 ?; apply: safe_step=>//; first by apply: immsafe_frame.
  move=>?? R; case: (red_frame _ _ _ _ _ R)=>// ?[?][?] EQ0; rewrite {}EQ0 in R *.
  by apply: H3.
Qed.

Lemma triple_frame: forall P c Q R,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄.
Proof.
move=>???? H ?[?][?][?][?][?]->.
apply: safe_frame=>//.
by apply: H.
Qed.

(** ** 2.3. The "small rules" for heap operations *)

Lemma triple_get: forall l v,
  ⦃ contains l v ⦄ GET l ⦃ fun v' => (v' = v) //\\ contains l v ⦄.
Proof.
move=>l v h P.
have L: h l = Some v by rewrite P hupdate_same.
apply: safe_step=>//.
- by apply: immsafe_get; rewrite L.
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (GET l, h)) (erefl (c', h'))=>// ??? E [EL EH][->->];
rewrite {}EL {}EH in E *; rewrite {}E in L; case: L=>->.
by apply: safe_done.
Qed.

Lemma triple_set: forall l v,
  ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄.
Proof.
move=>l v h [v0 P].
apply: safe_step=>//.
- by apply: immsafe_set; move/contains_eq: P=>->.
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (SET l v, h)) (erefl (c', h'))=>// ??? E [EL->EH][->->]; rewrite {}EL {}EH in E *.
apply: safe_done; rewrite P.
apply: heap_extensionality=>? /=.
by case: eqP.
Qed.

Fixpoint valid_N (l: addr) (sz: nat) : assertion :=
  match sz with O => emp | S sz => valid l ** valid_N (l + 1) sz end.

Remark valid_N_init: forall sz l,
  (valid_N l sz) (hinit l sz hempty).
Proof.
elim=>/=.
- by rewrite /emp.
- move=>sz ? l.
  exists (hsing l 0), (hinit (l + 1) sz hempty); do!split=>//.
  - by exists 0.
  - move=>? /=; case: eqP=>E; [right|left]=>//.
    by rewrite -E hinit_outside //; lia.
  by apply: heap_extensionality=>? /=; case: eqP.
Qed.

Lemma triple_alloc: forall sz,
  ⦃ emp ⦄
  ALLOC sz
  ⦃ fun l => (l <> 0) //\\ valid_N l sz ⦄.
Proof.
move=>sz ?->.
apply: safe_step=>//.
- by apply: (immsafe_alloc _ _ 1).
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (ALLOC sz, hempty)) (erefl (c', h'))=>// ??? H ?[ES EH][->->]; rewrite {}ES {}EH in H *.
apply: safe_done; split=>//.
by exact: valid_N_init.
Qed.

Lemma triple_free: forall l,
  ⦃ valid l ⦄
  FREE l
  ⦃ fun _ => emp ⦄.
Proof.
move=>l h [v0 P].
apply: safe_step=>//.
- by apply: immsafe_free; move/contains_eq: P=>->.
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (FREE l, h)) (erefl (c', h'))=>// ?? E [ES EH][->->]; rewrite {}ES {}EH in E *.
rewrite P; apply: safe_done.
by apply: heap_extensionality=>? /=; case: eqP.
Qed.

(** ** 2.4. Properties of the [safe] predicate *)

Lemma safe_pure: forall v h Q,
  safe (PURE v) h Q -> Q v h.
Proof.
move=>v ?? S.
case: {-2}_ _ _ / S (erefl (PURE v)).
- by move=>????; case=><-.
by move=>??? NP ?? E; rewrite E in NP.
Qed.

Lemma safe_red: forall c h Q c' h',
  safe c h Q -> red (c, h) (c', h') -> safe c' h' Q.
Proof.
move=>c h ??? S R.
case: {-1}_ {-1}_ _ / S (erefl c) (erefl h).
- move=>v ??? E ?; rewrite E in R.
  by case: {-1}_ _ / R (erefl (PURE v, h)).
move=>????? H EC EH.
by apply: H; rewrite -EC -EH.
Qed.

Lemma safe_immsafe: forall c h Q,
  safe c h Q -> immsafe (c, h).
Proof.
move=>???; case=>// ????.
by exact: immsafe_pure.
Qed.

Lemma safe_let: forall (Q R: postcond) f,
  (forall v h', Q v h' -> safe (f v) h' R) ->
  forall c h,
  safe c h Q ->
  safe (LET c f) h R.
Proof.
move=>Q ? f HP ?? S; elim: {-1}_ / S (erefl Q).
- move=>v h1 ?? E; apply: safe_step=>//; first by apply/immsafe_let/immsafe_pure.
  move=>c' h' R.
  case: {-2}_ {-1}_ / R (erefl (LET (PURE v) f, h1)) (erefl (c', h'))=>//.
  - move=>???; case=>->->->; case=>->->.
    by apply: HP; rewrite E.
  move=>????? R; case=>EC->EH; case=>->->; rewrite {}EC {}EH in R.
  by case: {-1}_ _ / R (erefl (PURE v, h1)).
- move=>c1 h1 ? NP ?? H2 ?; apply: safe_step=>//; first by apply: immsafe_let.
  move=>c' h' R.
  case: {-2}_ {-1}_ / R (erefl (LET c1 f, h1)) (erefl (c', h'))=>//.
  - by move=>???; case=>E; rewrite -E in NP.
  move=>????? R; case=>EC->EH; case=>->->; rewrite {}EC {}EH in R.
  by apply: H2.
Qed.

Lemma safe_consequence: forall (Q Q': postcond),
  (forall v, Q v -->> Q' v) ->
  forall c h, safe c h Q -> safe c h Q'.
Proof.
move=>Q ? I ?? S; elim: {-1}_ / S (erefl Q).
- by move=>???? E; apply/safe_done/I; rewrite E.
- by move=>?????? H3 ?; apply: safe_step=>// ???; apply: H3.
Qed.

(** ** 2.5. Rules for control structures *)

Lemma triple_pure: forall P v (Q: postcond),
  P -->> Q v ->
  ⦃ P ⦄ PURE v ⦃ Q ⦄.
Proof.
by move=>??? H ??; apply/safe_done/H.
Qed.

Lemma triple_let:
  forall c f (P: precond) (Q R: postcond),
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  (forall v, ⦃ Q v ⦄ f v ⦃ R ⦄) ->
  ⦃ P ⦄ LET c f ⦃ R ⦄.
Proof.
by move=>??? Q ? H ???; apply/(safe_let Q)/H.
Qed.

Lemma triple_ifthenelse: forall b c1 c2 P Q,
  ⦃ (b <> 0) //\\ P ⦄ c1 ⦃ Q ⦄ ->
  ⦃ (b = 0) //\\ P ⦄ c2 ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄.
Proof.
move=>b c1 c2 ?? H1 H2 h ?; apply: safe_step=>//.
- by exact: immsafe_ifthenelse.
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (IFTHENELSE b c1 c2, h)) (erefl (c', h'))=>// ????.
case=>->->->->; case=>->->.
by case: eqP=>?; [apply: H2|apply: H1].
Qed.

Lemma triple_consequence: forall P P' c Q' Q,
  ⦃ P' ⦄ c ⦃ Q' ⦄ ->
  P -->> P' -> (forall v, Q' v -->> Q v) ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
move=>????? H HP ???.
by apply/safe_consequence/H/HP.
Qed.

Lemma triple_pick: forall n,
  ⦃ emp ⦄
  PICK n
  ⦃ fun i => pure (0 <= i < n) ⦄.
Proof.
move=>n h ?; apply: safe_step=>//; first by exact: immsafe_pick.
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (PICK n, h)) (erefl (c', h'))=>// ??? LE.
case=>EN->; case=>->->; rewrite {}EN in LE.
by apply: safe_done.
Qed.

(** ** 2.6.  Useful derived rules *)

(** The following rules are heavily used in the examples of section 3. *)

Lemma triple_consequence_pre: forall P P' c Q,
  ⦃ P' ⦄ c ⦃ Q ⦄ ->
  P -->> P' ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
move=>? P' ? Q ???.
by apply: (triple_consequence _ P' _ Q)=>// ?.
Qed.

Lemma triple_consequence_post: forall P c Q Q',
  ⦃ P ⦄ c ⦃ Q' ⦄ ->
  (forall v, Q' v -->> Q v) ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
move=>P ? ? Q' ???.
by apply: (triple_consequence _ P _ Q').
Qed.

Lemma triple_lift_pure: forall (P: Prop) P' c Q,
  (P -> ⦃ P' ⦄ c ⦃ Q ⦄) ->
  ⦃ P //\\ P' ⦄ c ⦃ Q ⦄.
Proof.
by move=>???? H ?[??]; apply: H.
Qed.

Lemma triple_lift_exists: forall (X: Type) (P: X -> assertion) c Q,
  (forall x, ⦃ P x ⦄ c ⦃ Q ⦄) ->
  ⦃ aexists P ⦄ c ⦃ Q ⦄.
Proof.
by move=>???? H ?[? P]; apply/H/P.
Qed.

Lemma triple_ifthen: forall b c1 c2 P Q,
  b <> 0 -> ⦃ P ⦄ c1 ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄.
Proof.
move=>?????? H ? H2.
by apply/triple_ifthenelse/H2; apply: triple_lift_pure.
Qed.

Lemma triple_ifelse: forall b c1 c2 P Q,
  b = 0 -> ⦃ P ⦄ c2 ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄.
Proof.
move=>?????? H ? H2.
by apply/triple_ifthenelse/H2; apply: triple_lift_pure.
Qed.

Lemma unroll_com: forall c,
  c = match c with
      | PURE x => PURE x
      | LET c f => LET c f
      | IFTHENELSE b c1 c2 => IFTHENELSE b c1 c2
      | ALLOC sz => ALLOC sz
      | GET l => GET l
      | SET l v => SET l v
      | FREE l => FREE l
      | PICK n => PICK n
      end.
Proof. by case. Qed.

(** * 3. Singly-linked lists *)

(** ** Representation predicate *)

(** Here is a separation logic assertion that describes the in-memory
    representation of a list.
-   [a] is the pointer to the list head (or 0 if the list is empty).
-   [l] is the Coq list of the list elements.
*)

Fixpoint list_at (a: addr) (l: list int) : assertion :=
  match l with
  | nil => (a = 0) //\\ emp
  | h :: t => (a <> 0) //\\ aexists (fun a' => contains a h ** contains (a + 1) a' ** list_at a' t)
  end.

(** ** The "cons" operation *)

Definition list_cons (n: int) (a: addr) : com :=
  LET (ALLOC 2) (fun a' =>
  SEQ (SET a' n)
  (SEQ (SET (a' + 1) a)
  (PURE a'))).

Lemma list_cons_correct: forall a n l,
    ⦃ list_at a l ⦄
  list_cons n a
    ⦃ fun a' => list_at a' (n :: l) ⦄.
Proof.
move=>a ??? H; apply/triple_let/H.
- by rewrite -[list_at _ _]sepconj_emp; apply/triple_frame/triple_alloc.
move=>? /=; rewrite lift_pureconj !sepconj_assoc sepconj_emp.
apply: triple_lift_pure=>?.
apply: triple_let; first by apply/triple_frame/triple_set.
move=>? /=; apply: triple_let.
- by rewrite sepconj_pick2; apply/triple_frame/triple_set.
move=>? /=; rewrite sepconj_pick2; apply: triple_pure=>??; split=>//.
by exists a.
Qed.

(** ** Computing the length of a list *)

(** Taking advantage of the coinductive nature of type [com],
    we use infinite commands to represent loops and tail-recursive functions. *)

CoFixpoint list_length_rec (a: addr) (len: int) : com :=
  IFTHENELSE a (LET (GET (a + 1)) (fun t =>
                    list_length_rec t (len + 1)))
               (PURE len).

Definition list_length (a: addr) : com := list_length_rec a 0.

(** Normally we would write
<<
   len = 0;
   while (a != 0) { a = get (a + 1); len = len + 1; }
>>
   With the coinductive definition, we write the equivalent infinite command
<<
   if (a == 0) return 0; else {
     a1 = get (a + 1);
     if (a1 == 0) return 1; else {
       a2 = get (a1 + 1);
       if (a2 == 0) return 2; else ...
>>
*)

Lemma list_length_rec_correct: forall l a len,
    ⦃ list_at a l ⦄
  list_length_rec a len
    ⦃ fun len' => (len' = len + (length l)%:Z) //\\ list_at a l ⦄.
Proof.
elim=>[|?? IH] a len; rewrite (unroll_com (list_length_rec a len)) /=.
- apply: triple_lift_pure=>->; apply: triple_ifelse=>//.
  apply: triple_pure=>??; split=>//.
  by rewrite addr0.
apply: triple_lift_pure=>?; apply: triple_lift_exists=>x.
apply: triple_ifthen=>//; apply: triple_let.
- by rewrite sepconj_pick2; apply/triple_frame/triple_get.
move=>? /=; rewrite lift_pureconj; apply: triple_lift_pure=>->.
rewrite sepconj_swap3.
apply: triple_consequence_post; first by apply/triple_frame/IH.
move=>? /=; rewrite lift_pureconj -sepconj_swap3 sepconj_pick2.
move=>?[->?]; do!split=>//; first by rewrite -addrA.
by exists x.
Qed.

Corollary list_length_correct: forall l a,
    ⦃ list_at a l ⦄
  list_length a
    ⦃ fun len => (len = (length l)%:Z) //\\ list_at a l ⦄.
Proof.
by move=>????; apply: list_length_rec_correct.
Qed.

(** ** Concatenating two lists in-place *)

(** In loop notation:
<<
  if (l1 == 0) return l2; else {
    t = get(l1 + 1);
    while (get (t + 1) != 0) t = get (t + 1);
    set (t + 1, l2);
    return l1;
  }
>>
*)

CoFixpoint list_concat_rec (a1 a2: addr) : com :=
  LET (GET (a1 + 1))
      (fun t => IFTHENELSE t (list_concat_rec t a2)
                             (SET (a1 + 1) a2)).

Definition list_concat (a1 a2: addr) : com :=
  IFTHENELSE a1 (SEQ (list_concat_rec a1 a2)
                     (PURE a1))
                (PURE a2).

Lemma list_concat_rec_correct: forall l2 a2 l1 a1,
  a1 <> 0 ->
    ⦃ list_at a1 l1 ** list_at a2 l2 ⦄
  list_concat_rec a1 a2
    ⦃ fun _ => list_at a1 (l1 ++ l2) ⦄.
Proof.
move=>? a2; elim=>[|? t1 IH] a1 ?;
rewrite (unroll_com (list_concat_rec a1 a2)) /= lift_pureconj;
apply: triple_lift_pure=>? //.
rewrite lift_aexists; apply: triple_lift_exists=>x.
rewrite sepconj_assoc; apply: triple_let.
- by rewrite sepconj_assoc sepconj_pick2; apply/triple_frame/triple_get.
move=>? /=; rewrite lift_pureconj; apply: triple_lift_pure=>->.
apply: triple_ifthenelse; apply: triple_lift_pure=>?.
- rewrite -sepconj_assoc sepconj_comm.
  apply: triple_consequence_post; first by apply/triple_frame/IH.
  move=>?? /=; rewrite -sepconj_swap3 sepconj_pick2=>?; split=>//.
  by exists x.
apply: triple_consequence_post.
- apply/triple_frame/triple_consequence_pre; first by apply: triple_set.
  by move=>??; exists x.
move=>? /=; rewrite sepconj_pick2 sepconj_pick3.
case: {IH}t1=>[|??] /=; rewrite lift_pureconj ?sepconj_emp => ?[??] //.
by split=>//; exists a2.
Qed.

Lemma list_concat_correct: forall l1 a1 l2 a2,
    ⦃ list_at a1 l1 ** list_at a2 l2 ⦄
  list_concat a1 a2
    ⦃ fun a => list_at a (l1 ++ l2) ⦄.
Proof.
move=>l1 ???; rewrite /list_concat.
apply: triple_ifthenelse; apply: triple_lift_pure=>?.
- apply: triple_let; first by apply: list_concat_rec_correct.
  by move=>? /=; apply: triple_pure.
case: l1=>[|??] /=.
- by apply: triple_pure; rewrite lift_pureconj sepconj_emp=>?[??].
by rewrite lift_pureconj; apply: triple_lift_pure=>?.
Qed.

(** ** List reversal in place *)

(** In loop notation:
<<
  p = 0;
  while (l != 0) {
    n = get (l + 1);
    set (l + 1, p);
    p = l;
    l = n;
  }
  return p;
>>
*)

CoFixpoint list_rev_rec (a p: addr) : com :=
  IFTHENELSE a
    (LET (GET (a + 1)) (fun n =>
     SEQ (SET (a + 1) p)
         (list_rev_rec n a)))
    (PURE p).

Definition list_rev (a: addr) : com := list_rev_rec a 0.

Lemma list_rev_rec_correct: forall l a l' p,
    ⦃ list_at a l ** list_at p l' ⦄
  list_rev_rec a p
    ⦃ fun x => list_at x (List.rev_append l l') ⦄.
Proof.
elim=>[| ?? IH] a ? p; rewrite (unroll_com (list_rev_rec a p)) /=
  lift_pureconj ?sepconj_emp; apply: triple_lift_pure=>?.
- by apply/triple_ifelse/triple_pure.
rewrite lift_aexists; apply: triple_lift_exists=>x.
apply/triple_ifthen/triple_let=>//.
- rewrite !sepconj_assoc sepconj_pick2.
  by apply/triple_frame/triple_get.
move=>? /=; rewrite lift_pureconj; apply: triple_lift_pure=>->.
apply: triple_let.
- apply/triple_frame/triple_consequence_pre; first by apply: triple_set.
  by move=>??; exists x.
move=>? /=; rewrite sepconj_pick2 sepconj_pick3.
apply: triple_consequence_pre; first by apply: IH.
apply: sepconj_imp_r=>??; split=>//.
by exists p.
Qed.

Lemma list_rev_correct: forall a l,
    ⦃ list_at a l ⦄
  list_rev a
    ⦃ fun x => list_at x (rev l) ⦄.
Proof.
move=>??; apply: triple_consequence_pre; first by apply: list_rev_rec_correct.
by move=>?? /=; rewrite sepconj_comm lift_pureconj sepconj_emp.
Qed.

(** * 4. An alternate definition of separation logic triples *)

Module AlternateSeplog.

(** For some languages, the frame property for reductions (lemma
    [red_frame] above) does not hold, e.g. because allocations are
    deterministic.  Or maybe we do not want to prove the [red_frame]
    lemma.

    In this case, not all is lost: we can define our separation
    triples [ ⦃ P ⦄ c ⦃ Q ⦄ ] as Hoare triples plus framing. *)

Definition Hoare (P: precond) (c: com) (Q: postcond) : Prop :=
  forall h, P h -> safe c h Q.

Definition triple (P: precond) (c: com) (Q: postcond) :=
  forall (R: assertion), Hoare (P ** R) c (fun v => Q v ** R).

Notation "⦃ P ⦄ c ⦃ Q ⦄" := (triple P c Q) (at level 90, c at next level).

(** This definition validates the frame rule. *)

Lemma triple_frame: forall P c Q R,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  ⦃ P ** R ⦄ c ⦃ fun v => Q v ** R ⦄.
Proof.
move=>?? Q R TR R' ?.
rewrite sepconj_assoc=>?.
rewrite (_ : (fun v => (Q v ** R) ** R') = (fun v => Q v ** (R ** R'))); first by apply: TR.
by apply: functional_extensionality=>?; rewrite sepconj_assoc.
Qed.

(** It also validates the "small rules" for heap operations. *)

Lemma triple_get: forall l v,
  ⦃ contains l v ⦄ GET l ⦃ fun v' => (v' = v) //\\ contains l v ⦄.
Proof.
move=>l v ? h[h1][h2][H1][?][?]E.
have L: h l = Some v by rewrite E /=; move/contains_eq: H1=>->.
apply: safe_step=>//.
- by apply: immsafe_get; rewrite L.
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (GET l, h)) (erefl (c', h'))=>// ??? E2 [EL EH][->->];
rewrite {}EL {}EH in E2 *; rewrite {}E2 in L; case: L=>->.
apply: safe_done; rewrite E.
by exists h1, h2.
Qed.

Lemma triple_set: forall l v,
  ⦃ valid l ⦄ SET l v ⦃ fun _ => contains l v ⦄.
Proof.
move=>l v ? h [h1][h2][[v0 H1]][?][D]E.
have L: h l = Some v0 by rewrite E /=; move/contains_eq: H1=>->.
apply: safe_step=>//.
- by apply: immsafe_set; rewrite L.
rewrite /contains in H1.
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (SET l v, h)) (erefl (c', h'))=>// ??? _ [->->->][->->]; rewrite E.
apply: safe_done.
exists (hsing l v), h2; do!split=>//.
- move=>/= l'; case: (D l')=>EH1; last by right.
  case: eqP=>EL; last by left.
  by move: EH1; rewrite -EL; move/contains_eq: H1=>->.
apply: heap_extensionality=>? /=; case: ifP=>//=.
by rewrite H1 /= =>->.
Qed.

Remark valid_N_init:
  forall (R: assertion) sz l h,
  R h ->
  (forall i, l <= i < l + sz%:Z -> h i = None) ->
  (valid_N l sz ** R) (hinit l sz h).
Proof.
move=>?; elim=>[| sz IH] l h ? HE /=.
- by rewrite sepconj_emp.
rewrite sepconj_assoc.
exists (hsing l 0), (hinit (l + 1) sz h); do!split.
- by exists 0.
- by apply: IH=>// ??; apply: HE; lia.
- move=>? /=; case: eqP; [move=><-;right|left]=>//.
  by rewrite hinit_outside; [apply: HE|]; lia.
by apply: heap_extensionality=>? /=; case: eqP.
Qed.

Lemma triple_alloc: forall sz,
  ⦃ emp ⦄
  ALLOC sz
  ⦃ fun l => (l <> 0) //\\ valid_N l sz ⦄.
Proof.
move=>sz ? h; rewrite sepconj_emp => ?.
apply: safe_step=>//.
- case: (isfinite h)=>l0 F.
  apply: (immsafe_alloc _ _ (Num.max l0 1)); first by lia.
  by move=>??; apply: F; lia.
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (ALLOC sz, h)) (erefl (c', h'))=>// ??? F ? [ES EH][->->]; rewrite {}ES {}EH in F *.
apply: safe_done; rewrite lift_pureconj; split=>//.
by exact: valid_N_init.
Qed.

Lemma triple_free: forall l,
  ⦃ valid l ⦄
  FREE l
  ⦃ fun _ => emp ⦄.
Proof.
move=>l ? h [h1][h2][[v0 H1]][?][D]E.
have L: h l = Some v0 by rewrite E /=; move/contains_eq: H1=>->.
apply: safe_step=>//.
- by apply: immsafe_free; rewrite L.
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (FREE l, h)) (erefl (c', h'))=>// ?? H [EL EH][->->]; rewrite {}EL {}EH in H *.
apply: safe_done; rewrite sepconj_emp E.
rewrite (_ : hfree l (hunion h1 h2) = h2) //.
apply: heap_extensionality=>l'.
by case: (D l'); rewrite H1 /=; case: eqP=>/=.
Qed.

(** The rules for control structures are also valid.
    Proof plan: first show Hoare-style rules for the [Hoare] triple,
    then frame by an arbitrary [R] to obtain the separation triple. *)

Lemma Hoare_pure: forall P v (Q: postcond),
  P -->> Q v ->
  Hoare P (PURE v) Q.
Proof.
by move=>??? H ??; apply/safe_done/H.
Qed.

Lemma triple_pure: forall P v (Q: postcond),
  P -->> Q v ->
  ⦃ P ⦄ PURE v ⦃ Q ⦄.
Proof.
by move=>?????; apply/Hoare_pure/sepconj_imp_l.
Qed.

Lemma Hoare_let:
  forall c f (P: precond) (Q R: postcond),
  Hoare P c Q ->
  (forall v, Hoare (Q v) (f v) R) ->
  Hoare P (LET c f) R.
Proof.
move=>??? Q ? H1 H2 ??.
by apply: (safe_let Q); [apply: H2 | apply: H1].
Qed.

Lemma triple_let:
  forall c f (P: precond) (Q R: postcond),
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  (forall v, ⦃ Q v ⦄ f v ⦃ R ⦄) ->
  ⦃ P ⦄ LET c f ⦃ R ⦄.
Proof.
move=>??? Q ? H1 H2 R'.
by apply: (Hoare_let _ _ _ (fun v => Q v ** R')); [apply: H1 | move=>?; apply: H2].
Qed.

Lemma Hoare_ifthenelse: forall b c1 c2 P Q,
  Hoare ((b <> 0) //\\ P) c1 Q ->
  Hoare ((b = 0) //\\ P) c2 Q ->
  Hoare P (IFTHENELSE b c1 c2) Q.
Proof.
move=>b c1 c2 ?? H1 H2 h ?.
apply: safe_step=>//; first by apply: immsafe_ifthenelse.
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (IFTHENELSE b c1 c2, h)) (erefl (c', h'))=>// ????[->->->->][->->].
by case: eqP=>?; [apply: H2|apply: H1].
Qed.

Lemma triple_ifthenelse: forall b c1 c2 P Q,
  ⦃ (b <> 0) //\\ P ⦄ c1 ⦃ Q ⦄ ->
  ⦃ (b = 0) //\\ P ⦄ c2 ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄.
Proof.
by move=>????????; apply: Hoare_ifthenelse; rewrite -lift_pureconj.
Qed.

Lemma Hoare_consequence: forall P P' c Q' Q,
  Hoare P' c Q' ->
  P -->> P' -> (forall v, Q' v -->> Q v) ->
  Hoare P c Q.
Proof.
by move=>??? Q' ? H H1 ???; apply/(safe_consequence Q')/H/H1.
Qed.

Lemma triple_consequence: forall P P' c Q' Q,
  ⦃ P' ⦄ c ⦃ Q' ⦄ ->
  P -->> P' -> (forall v, Q' v -->> Q v) ->
  ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
move=>? P' ? Q' ???? R; apply: (Hoare_consequence _ (P' ** R) _ (fun v => Q' v ** R)) => //.
- by apply: sepconj_imp_l.
by move=>?; apply: sepconj_imp_l.
Qed.

Lemma Hoare_pick: forall P n,
  Hoare P (PICK n) (fun i => (0 <= i < n) //\\ P).
Proof.
move=>? n h ?; apply: safe_step=>//; first by exact: immsafe_pick.
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (PICK n, h)) (erefl (c', h'))=>// ??? H [EN->][->->]; rewrite {}EN in H.
by apply: safe_done.
Qed.

Lemma triple_pick: forall n,
  ⦃ emp ⦄
  PICK n
  ⦃ fun i => pure (0 <= i < n) ⦄.
Proof.
move=>? R; rewrite sepconj_emp.
apply: (Hoare_consequence _ R)=>//; first by exact: Hoare_pick.
by move=>???; rewrite pureconj_sepconj.
Qed.

End AlternateSeplog.

(** * 5. Ramification *)

(** Assume we have a triple [{P'} c {Q'}] and we want to conclude [{P} c {Q}].
    In general, we need to frame the former triple by an appropriate [R],
    then use the consequence rule to conclude. *)

Lemma triple_frame_consequence: forall R P c Q P' Q',
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  P' -->> P ** R ->
  (forall v, Q v ** R -->> Q' v) ->
  ⦃ P' ⦄ c ⦃ Q' ⦄.
Proof.
by move=>??????? H1 H2; apply/triple_consequence/H2/H1/triple_frame.
Qed.

(** This rule still needs the user to guess the framing predicate [R].
    An alternate presentation uses the magic wand instead.
    This approach is called "ramification" in the literature. *)

Lemma triple_ramification: forall P c Q P' Q',
 ⦃ P ⦄ c ⦃ Q ⦄ ->
  P' -->> P ** (aforall (fun v => Q v --* Q' v)) ->
  ⦃ P' ⦄ c ⦃ Q' ⦄.
Proof.
move=>P ? Q ? Q' ??.
apply: (triple_frame_consequence (aforall (fun v => Q v --* Q' v)) P _ Q)=>//.
move=>v ?[h1][h2][?][?][?]->; apply: (wand_cancel (Q v)).
by exists h1, h2.
Qed.

(** * 6. Weakest preconditions *)

(** ** 6.1.  Definition and characterization *)

(** Here is one possible definition of the weakest precondition for
    command [c] with postcondition [Q]. *)

Definition wp (c: com) (Q: postcond) : precond :=
  aexists (fun P => ⦃ P ⦄ c ⦃ Q ⦄ //\\ P).

(** What matters about [wp c Q] is that it is a precondition... *)

Lemma wp_precond: forall c Q,
  ⦃ wp c Q ⦄ c ⦃ Q ⦄.
Proof. by move=>???[?][T]?; apply: T. Qed.

(** ... and it is implied by any other precondition. *)

Lemma wp_weakest: forall P c Q,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  P -->> wp c Q.
Proof. by move=>P ?????; exists P. Qed.

(** This leads to the following alternate definition of triples in terms
    of weakest preconditions. *)

Corollary wp_equiv: forall P c Q,
  ⦃ P ⦄ c ⦃ Q ⦄ <-> (P -->> wp c Q).
Proof.
move=>? c Q; split=>?? H2.
- by apply/wp_weakest/H2.
apply/(triple_consequence_pre _ (wp c Q))/H2=>//.
by exact: wp_precond.
Qed.

(** Here is another definition of the weakest precondition, using the
    operational semantics directly. *)

Definition wp' (c: com) (Q: postcond) : precond :=
  fun h => safe c h Q.

Lemma wp'_precond: forall c Q,
  ⦃ wp' c Q ⦄ c ⦃ Q ⦄.
Proof. by move=>???; apply. Qed.

Lemma wp'_weakest: forall P c Q,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  P -->> wp' c Q.
Proof. by move=>??? H ??; apply: H. Qed.

(** ** 6.2. Structural rules for weakest preconditions *)

Lemma wp_consequence: forall (Q Q': postcond) c,
  (forall v, Q v -->> Q' v) ->
  wp c Q -->> wp c Q'.
Proof.
move=>Q ???; apply/wp_weakest/(triple_consequence_post _ _ _ Q)=>//.
by exact: wp_precond.
Qed.

Lemma wp_frame: forall R c Q,
  wp c Q ** R -->> wp c (fun v => Q v ** R).
Proof. by move=>???; apply/wp_weakest/triple_frame/wp_precond. Qed.

Corollary wp_frame_consequence: forall R Q c Q',
  (forall v, Q v ** R -->> Q' v) ->
  wp c Q ** R -->> wp c Q'.
Proof.
move=>???? H ??; apply: wp_consequence; first by exact: H.
by apply: wp_frame.
Qed.

Corollary wp_ramification: forall c Q Q',
  wp c Q ** aforall (fun v => Q v --* Q' v) -->> wp c Q'.
Proof.
move=>? Q ?; apply: wp_frame_consequence=>v ?[h1][h2][?][?][?]->.
apply: (wand_cancel (Q v)).
by exists h1, h2.
Qed.

(** ** 6.3.  Weakest precondition rules for our language of pointers *)

Lemma wp_pure: forall (Q: postcond) v,
  Q v -->> wp (PURE v) Q.
Proof. by move=>??? H; apply/wp_weakest/H/triple_pure. Qed.

Lemma wp_let: forall c f Q,
  wp c (fun v => wp (f v) Q) -->> wp (LET c f) Q.
Proof.
move=>????; apply/wp_weakest/triple_let; first by exact: wp_precond.
by move=>?; apply: wp_precond.
Qed.

Lemma wp_ifthenelse: forall b c1 c2 Q,
  (if b == 0 then wp c2 Q else wp c1 Q) -->> wp (IFTHENELSE b c1 c2) Q.
Proof.
move=>? c1 c2 Q; apply/wp_weakest/triple_ifthenelse.
- apply: (triple_consequence_pre _ (wp c1 Q)); first by exact: wp_precond.
  by move=>?[/eqP/negbTE->].
apply: (triple_consequence_pre _ (wp c2 Q)); first by exact: wp_precond.
by move=>?[/eqP->].
Qed.

Lemma wp_alloc: forall sz Q,
  aforall (fun l => (l <> 0) //\\ valid_N l sz --* Q l) -->> wp (ALLOC sz) Q.
Proof.
move=>sz ???.
apply: (wp_ramification _ (fun l => (l <> 0) //\\ valid_N l sz)).
apply: (sepconj_imp_l emp).
- by apply/wp_weakest/triple_alloc.
by rewrite sepconj_emp.
Qed.

Lemma wp_get: forall l v Q,
  contains l v ** (contains l v --* Q v) -->> wp (GET l) Q.
Proof.
move=>l v ?? H.
have W: contains l v -->> wp (GET l) (fun v' => (v' = v) //\\ contains l v)
  by apply/wp_weakest/triple_get.
apply/wp_ramification/sepconj_imp_l; first by exact: W.
apply/sepconj_imp_r/H => ? H2 ???[->?].
by apply: H2.
Qed.

Lemma wp_set: forall l v Q,
  valid l ** aforall (fun v' => (contains l v --* Q v')) -->> wp (SET l v) Q.
Proof.
move=>l v ?? H.
have W: valid l -->> wp (SET l v) (fun _ => contains l v)
  by apply/wp_weakest/triple_set.
apply/wp_ramification/sepconj_imp_l; first by exact: W.
by apply/sepconj_imp_r/H.
Qed.

Corollary wp_set': forall l v Q,
  valid l ** (contains l v --* Q) -->> wp (SET l v) (fun _ => Q).
Proof. by move=>???? H; apply/wp_set/sepconj_imp_r/H=>??. Qed.

Lemma wp_free: forall l Q,
  valid l ** aforall (fun v' => Q v') -->> wp (FREE l) Q.
Proof.
move=>l ?? H.
have W: valid l -->> wp (FREE l) (fun _ => emp)
 by apply/wp_weakest/triple_free.
apply/wp_ramification/sepconj_imp_l; first by exact: W.
apply/sepconj_imp_r/H=>???? H2 E.
rewrite E in H2 *; move/hdisjoint_sym: H2=>H2.
by rewrite hunion_comm // hunion_empty.
Qed.

Corollary wp_free': forall l Q,
  valid l ** Q -->> wp (FREE l) (fun _ => Q).
Proof. by move=>??? H; apply/wp_free/sepconj_imp_r/H=>??. Qed.

Lemma wp_pick: forall n Q,
  aforall (fun i => pure (0 <= i < n) --* Q i) -->> wp (PICK n) Q.
Proof.
move=>n ?? H.
have W: emp -->> wp (PICK n) (fun i => pure (0 <= i < n))
  by apply/wp_weakest/triple_pick.
apply/wp_ramification/sepconj_imp_l; first by exact: W.
by apply: sepconj_imp_r; last by rewrite sepconj_emp; exact: H.
Qed.
