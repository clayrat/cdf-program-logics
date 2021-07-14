(** Separation logic (simplified). *)

From Coq Require Import ssreflect ssrfun ssrbool Lia FunctionalExtensionality PropExtensionality.
From mathcomp Require Import ssrint ssrnum ssralg seq eqtype order zify.
From CDF Require Import Separation.
Import Order.Theory.
Import GRing.Theory.
Local Open Scope ring_scope.

(** * 1. A language of pointers *)

(** We now define a small programming language to work with pointers to
    mutable state. The language has variables, but these variables are
    immutable. This in unlike IMP but like ML: mutable variables are
    expressed as immutable pointers (references) to mutable state. *)

(** As in ML too, we blur the distinction between expressions and commands.
    Every command returns a value, which we take to be an integer,
    in addition to possibly performing effects. *)

(** We use higher-order abstract syntax to represent commands in this
    language. With first-order abstract syntax, a "let" binding
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
  | IFTHENELSE (b: int) (c1 c2: com)    (**r conditional, IF B!=0 THEN C1 ELSE C2 *)
  | ALLOC (sz: nat)                     (**r allocate [sz] words of storage *)
  | GET (l: addr)                       (**r dereference a pointer *)
  | SET (l: addr) (v: int)              (**r assign through a pointer *)
  .

Definition not_pure (c : com) :=
  if c is PURE _ then false else true.

(** Some derived forms. *)

Definition SKIP: com := PURE 0.

Definition SEQ (c1 c2: com) := LET c1 (fun _ => c2).

(** Reduction semantics. *)

Inductive red: com * heap -> com * heap -> Prop :=
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
      red (SET l v, h) (SKIP, hupdate l v h).

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
      h l <> None -> immsafe (SET l v, h).

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

(** We define semantic triples: *)

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
Qed.

Lemma red_frame: forall h2 c h1 c' h',
  red (c, hunion h1 h2) (c', h') ->
  immsafe (c, h1) ->
  hdisjoint h1 h2 ->
  exists h1', red (c, h1) (c', h1') /\ hdisjoint h1' h2 /\ h' = hunion h1' h2.
Proof.
move=>h2 ? h1 ? h' R; dependent induction R => I HD.
- case: {-2}_ / I (erefl (LET (PURE x) f, h1))=>// ??? I [EC->EH]; rewrite {}EC {}EH in I *.
  by exists h1; do!split=>//; exact: red_let_done.
- case: {-2}_ / I (erefl (LET c f, h1))=>// c0 ?? I [EC->EH]; rewrite {}EC {}EH in I IHR *.
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
- case: {-2}_ / I (erefl (GET l, h1))=>// ?? EQ [EL EH]; rewrite {}EL {}EH in EQ *.
  exists h1; do!split=>//; apply: red_get.
  by move: H=>/=; case E: (h1 l).
- case: {-2}_ / I (erefl (SET l v, h1))=>// ??? EQ [EL->EH]; rewrite {}EL {}EH in EQ *.
  exists (hupdate l v h1); do!split.
  - by apply: red_set.
  - move=>i; move: (HD i)=>/=; case=>?; try by right.
    case: eqP; try by left.
    by move=>E; rewrite E in EQ.
  apply: heap_extensionality=>i /=.
  by case: eqP.
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
  ⦃ contains l v ⦄ GET l ⦃ fun v' => (v' = v) /\\ contains l v ⦄.
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
by apply: heap_extensionality=>? /=; case: eqP.
Qed.

(* sz consecutive addresses starting from l are valid *)
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
  ⦃ fun l => (l <> 0) /\\ valid_N l sz ⦄.
Proof.
move=>sz ?->.
apply: safe_step=>//.
- by apply: (immsafe_alloc _ _ 1).
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (ALLOC sz, hempty)) (erefl (c', h'))=>// ??? H ?[ES EH][->->]; rewrite {}ES {}EH in H *.
apply: safe_done; split=>//.
by exact: valid_N_init.
Qed.

(** ** 2.4. Properties of the [safe] predicate *)

Lemma safe_pure: forall v h Q,
  safe (PURE v) h Q -> Q v h.
Proof.
move=>v ?? S.
case: {-2}_ _ _ / S (erefl (PURE v)).
- by move=>???? [<-].
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
  - move=>???[->->->][->->].
    by apply: HP; rewrite E.
  move=>????? R [EC->EH][->->]; rewrite {}EC {}EH in R.
  by case: {-1}_ _ / R (erefl (PURE v, h1)).
- move=>c1 h1 ? NP ?? H2 ?; apply: safe_step=>//; first by apply: immsafe_let.
  move=>c' h' R.
  case: {-2}_ {-1}_ / R (erefl (LET c1 f, h1)) (erefl (c', h'))=>//.
  - by move=>??? [E]; rewrite -E in NP.
  move=>????? R [EC->EH][->->]; rewrite {}EC {}EH in R.
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
Proof. by move=>??? H ??; apply/safe_done/H. Qed.

Lemma triple_let:
  forall c f (P: precond) (Q R: postcond),
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  (forall v, ⦃ Q v ⦄ f v ⦃ R ⦄) ->
  ⦃ P ⦄ LET c f ⦃ R ⦄.
Proof.
by move=>??? Q ? H ???; apply/(safe_let Q)/H.
Qed.

Lemma triple_ifthenelse: forall b c1 c2 P Q,
  ⦃ (b <> 0) /\\ P ⦄ c1 ⦃ Q ⦄ ->
  ⦃ (b = 0) /\\ P ⦄ c2 ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄.
Proof.
move=>b c1 c2 ?? H1 H2 h ?; apply: safe_step=>//.
- by exact: immsafe_ifthenelse.
move=>c' h' R.
case: {-2}_ {-1}_ / R (erefl (IFTHENELSE b c1 c2, h)) (erefl (c', h'))=>// ???? [->->->->][->->].
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
move=>P ?? Q' ???.
by apply: (triple_consequence _ P _ Q').
Qed.

Lemma triple_lift_pure: forall (P: Prop) P' c Q,
  (P -> ⦃ P' ⦄ c ⦃ Q ⦄) ->
  ⦃ P /\\ P' ⦄ c ⦃ Q ⦄.
Proof. by move=>???? H ?[??]; apply: H. Qed.

Lemma triple_lift_exists: forall (X: Type) (P: X -> assertion) c Q,
  (forall x, ⦃ P x ⦄ c ⦃ Q ⦄) ->
  ⦃ aexists P ⦄ c ⦃ Q ⦄.
Proof. by move=>???? H ?[? P]; apply/H/P. Qed.

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
      end.
Proof. by case. Qed.

(** * 3. Singly-linked lists *)

(** ** Representation predicate *)

(** Here is a separation logic assertion that describes the in-memory
    representation of a list.
-   [a] is the pointer to the list head (or 0 if the list is empty).
-   [l] is the Coq list of the list elements.
*)

Fixpoint list_at (a: addr) (l: seq int) : assertion :=
  match l with
  | nil => pure (a = 0)
  | h :: t => (a <> 0) /\\ aexists (fun a2 => contains a h ** contains (a + 1) a2 ** list_at a2 t)
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
move=>a ??? H. apply/triple_let/H.
- by rewrite -[list_at _ _]sepconj_emp; apply/triple_frame/triple_alloc.
move=>a2 /=; rewrite lift_pureconj !sepconj_assoc sepconj_emp.
apply: triple_lift_pure=>?.
apply: triple_let.
- by apply/triple_frame/triple_set.
move=>? /=. apply: triple_let.
- by rewrite sepconj_pick2; apply/triple_frame/triple_set.
move=>? /=. rewrite sepconj_pick2; apply: triple_pure =>/=??; split=>//.
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
    ⦃ fun len' => (len' = len + (length l)%:Z) /\\ list_at a l ⦄.
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
    ⦃ fun len => (len = (length l)%:Z) /\\ list_at a l ⦄.
Proof. by move=>????; apply: list_length_rec_correct. Qed.

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

CoFixpoint list_rev_rec (i done : addr) : com :=
  IFTHENELSE i
    (LET (GET (i + 1)) (fun k =>
     SEQ (SET (i + 1) done)
         (list_rev_rec k i)))
    (PURE done).

Definition list_rev (i: addr) : com := list_rev_rec i 0.

Lemma list_rev_rec_correct: forall l i lrev done,
    ⦃ list_at i l ** list_at done lrev ⦄
  list_rev_rec i done
    ⦃ fun x => list_at x (List.rev_append l lrev) ⦄.
Proof.
elim=>[| hd tl IH] i ? done; rewrite (unroll_com (list_rev_rec i done)) /=
  lift_pureconj ?sepconj_emp; apply: triple_lift_pure=>? /=.
- by apply/triple_ifelse/triple_pure.
rewrite lift_aexists; apply: triple_lift_exists=>x.
apply/triple_ifthen/triple_let=>//.
- rewrite !sepconj_assoc sepconj_pick2.
  by apply/triple_frame/triple_get.
move=>? /=. rewrite lift_pureconj; apply: triple_lift_pure=>->.
apply: triple_let.
- apply/triple_frame/triple_consequence_pre; first by apply: triple_set.
  by move=>??; exists x.
move=>? /=. rewrite sepconj_pick2 sepconj_pick3.
apply: triple_consequence_pre; first by apply: IH.
apply: sepconj_imp_r=>??/=. split=>//.
by exists done.
Qed.

Lemma list_rev_correct: forall i l,
    ⦃ list_at i l ⦄
  list_rev i
    ⦃ fun done => list_at done (rev l) ⦄.
Proof.
move=>??; apply: triple_consequence_pre; first by apply: list_rev_rec_correct.
by move=>?? /=; rewrite sepconj_comm lift_pureconj sepconj_emp.
Qed.
