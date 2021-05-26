(** Hoare logic. *)

From Coq Require Import ssreflect ssrfun ssrbool String Lia FunctionalExtensionality.
From mathcomp Require Import ssrnat ssrint ssrnum ssralg eqtype order zify.
From Paco Require Import paco.
From CDF Require Import Sequences.
Import Order.Theory.
Local Open Scope ring_scope.

(* TODO move to Util *)

Theorem well_founded_rlt : well_founded (fun n m : int => 0 <= n < m).
Proof.
  move => x.
  move: {2}x (lexx x) => n.
  elim: n x => [| n IHn| n IHn] x H; constructor => y H0.
  - by apply False_ind; lia.
  - by apply IHn; lia.
  - by apply IHn; lia.
Defined.

Definition eq_string (a b : string) : bool :=
  match string_dec a b with left _ => true| right _ => false end.

Lemma eq_string_refl : forall s, eq_string s s.
Proof.
elim=> // h t; rewrite /eq_string.
case: (string_dec _ _) => // _ _; by case: (string_dec _ _).
Qed.

Lemma eq_stringP : Equality.axiom eq_string.
Proof. move=> x y; apply: (iffP idP); rewrite /eq_string; by case: (string_dec _ _). Qed.

Canonical Structure string_eqMixin := EqMixin eq_stringP.
Canonical Structure string_eqType := Eval hnf in EqType _ string_eqMixin.

Ltac inv H := inversion H; clear H; subst.

(** * 1.  The IMP language *)

(** ** 1.1. Arithmetic expressions *)

Definition ident := string.

(** The abstract syntax: an arithmetic expression is either... *)

Inductive aexp : Type :=
  | CONST (n: int)                     (**r a constant, or *)
  | VAR (x: ident)                     (**r a variable, or *)
  | PLUS (a1: aexp) (a2: aexp)         (**r a sum of two expressions, or *)
  | MINUS (a1: aexp) (a2: aexp).       (**r a difference of two expressions *)

(** The denotational semantics: an evaluation function that computes
  the integer value denoted by an expression.  This function is
  parameterized by a store [s] that associates values to variables. *)

Definition store : Type := ident -> int.

Fixpoint aeval (a: aexp) (s: store) : int :=
  match a with
  | CONST n => n
  | VAR x => s x
  | PLUS a1 a2 => aeval a1 s + aeval a2 s
  | MINUS a1 a2 => aeval a1 s - aeval a2 s
  end.

(** ** 1.2. Boolean expressions *)

(** The IMP language has conditional statements (if/then/else) and
  loops.  They are controlled by expressions that evaluate to Boolean
  values.  Here is the abstract syntax of Boolean expressions. *)

Inductive bexp : Type :=
  | TRUE                              (**r always true *)
  | FALSE                             (**r always false *)
  | EQUAL (a1: aexp) (a2: aexp)       (**r whether [a1 = a2] *)
  | LESSEQUAL (a1: aexp) (a2: aexp)   (**r whether [a1 <= a2] *)
  | NOT (b1: bexp)                    (**r Boolean negation *)
  | AND (b1: bexp) (b2: bexp).        (**r Boolean conjunction *)

(** Just like arithmetic expressions evaluate to integers,
  Boolean expressions evaluate to Boolean values [true] or [false]. *)

Fixpoint beval (b: bexp) (s: store) : bool :=
  match b with
  | TRUE => true
  | FALSE => false
  | EQUAL a1 a2 => aeval a1 s == aeval a2 s
  | LESSEQUAL a1 a2 => aeval a1 s <= aeval a2 s
  | NOT b1 => negb (beval b1 s)
  | AND b1 b2 => beval b1 s && beval b2 s
  end.

(** There are many useful derived forms. *)

Definition NOTEQUAL (a1 a2: aexp) : bexp := NOT (EQUAL a1 a2).

Definition GREATEREQUAL (a1 a2: aexp) : bexp := LESSEQUAL a2 a1.

Definition GREATER (a1 a2: aexp) : bexp := NOT (LESSEQUAL a1 a2).

Definition LESS (a1 a2: aexp) : bexp := GREATER a2 a1.

Definition OR (b1 b2: bexp) : bexp := NOT (AND (NOT b1) (NOT b2)).

(** ** 1.3. Commands *)

(** To complete the definition of the IMP language, here is the
  abstract syntax of commands, also known as statements. *)

Inductive com: Type :=
  | SKIP                                     (**r do nothing *)
  | ASSIGN (x: ident) (a: aexp)              (**r assignment: [v := a] *)
  | SEQ (c1: com) (c2: com)                  (**r sequence: [c1; c2] *)
  | IFTHENELSE (b: bexp) (c1: com) (c2: com) (**r conditional: [if b then c1 else c2] *)
  | WHILE (b: bexp) (c1: com)                (**r loop: [while b do c1 done] *)
  | ASSERT (b: bexp)                         (**r assertion (error if false) *)
  | HAVOC (x: ident).                        (**r nondeterministic assignment *)

(** We can write [c1 ;; c2] instead of [SEQ c1 c2], it is easier on the eyes. *)

Infix ";;" := SEQ (at level 80, right associativity).

(** Reduction semantics. *)

Definition update (x: ident) (v: int) (s: store) : store :=
  fun y => if x == y then v else s y.

Lemma update_same: forall x v s, (update x v s) x = v.
Proof.
by rewrite /update=>???; rewrite eq_refl.
Qed.

Lemma update_other: forall x v s y, x <> y -> (update x v s) y = s y.
Proof.
by rewrite /update=>?????; case: eqP.
Qed.

(** The relation [ red (c, s) (c', s') ], written [ c / s --> c' / s' ]
    in the lectures, defines a basic reduction, that is, the first
    computation step when executing command [c] in initial memory
    state [s].
    [s'] is the memory state "after" this computation step.
    [c'] is a command that represent all the computations that remain
    to be performed later.

    The reduction relation is presented as a Coq inductive predicate,
    with one case (one "constructor") for each reduction rule.
*)

Inductive red: com * store -> com * store -> Prop :=
  | red_assign: forall x a s,
      red (ASSIGN x a, s) (SKIP, update x (aeval a s) s)
  | red_seq_done: forall c s,
      red (SEQ SKIP c, s) (c, s)
  | red_seq_step: forall c1 c s1 c2 s2,
      red (c1, s1) (c2, s2) ->
      red (SEQ c1 c, s1) (SEQ c2 c, s2)
  | red_ifthenelse: forall b c1 c2 s,
      red (IFTHENELSE b c1 c2, s) ((if beval b s then c1 else c2), s)
  | red_while_done: forall b c s,
      ~~ beval b s ->
      red (WHILE b c, s) (SKIP, s)
  | red_while_loop: forall b c s,
      beval b s ->
      red (WHILE b c, s) (SEQ c (WHILE b c), s)
  | red_havoc: forall x s n,
      red (HAVOC x, s) (SKIP, update x n s)
  | red_assert: forall b s,
      beval b s ->
      red (ASSERT b, s) (SKIP, s).

(** The predicate [ error c s ] means that command [c] started in state [s]
    causes a run-time error.
    This is written [ c / s --> err ] in the lectures. *)

Fixpoint error (c: com) (s: store) : Prop :=
  match c with
  | ASSERT b => ~~ beval b s
  | (c1 ;; c2) => error c1 s
  | _ => False
  end.

Definition terminated (c: com) : Prop := c = SKIP.

Definition terminates (c: com) (s s': store) : Prop :=
  exists c', star red (c, s) (c', s') /\ terminated c'.

Definition goeswrong (c: com) (s: store) : Prop :=
  exists c' s', star red (c, s) (c', s') /\ error c' s'.

(** * 2.  Hoare logic *)

(** ** 2.1.  Assertions on the values of variables *)

(** Hoare logic manipulates formulas / claims / assertions that "talk about"
    the values of the program variables.  A typical assertion is
    [0 <= x /\ x <= y], meaning "at this program point, the value of
    variable [x] is positive and less than or equal to the value of
    variable [y]". *)

(** In our Coq development, we represent assertions by Coq logical formulas
    (type [Prop]) parameterized by the current store, which provides
    the values of the variables.

    For example, the assertion [0 <= x /\ x <= y] above is represented
    by the Coq predicate [fun s => 0 <= s "x" /\ s "x" <= s "y"]. *)

Definition assertion : Type := store -> Prop.

(** Here are some useful assertions.
    Conjunction and disjunction of two assertions. *)

Definition aand (P Q: assertion) : assertion :=
  fun s => P s /\ Q s.

Definition aor (P Q: assertion) : assertion :=
  fun s => P s \/ Q s.

(** The assertion "arithmetic expression [a] evaluates to value [v]". *)

Definition aequal (a: aexp) (v: int) : assertion :=
  fun s => aeval a s = v.

(** The assertions "Boolean expression [b] evaluates to true / to false". *)

Definition atrue (b: bexp) : assertion :=
  fun s => beval b s.

Definition afalse (b: bexp) : assertion :=
  fun s => ~~ beval b s.

(** The assertion written "[ P[x <- a] ]" in the literature.
    Substituting [a] for [x] in [P] amounts to evaluating [P] in
    stores where the variable [x] is equal to the value of expression [a]. *)

Definition aupdate (x: ident) (a: aexp) (P: assertion) : assertion :=
  fun s => P (update x (aeval a s) s).

(** Pointwise implication.  Unlike conjunction and disjunction, this is
    not a predicate over the store, just a Coq proposition. *)

Definition aimp (P Q: assertion) : Prop :=
  forall s, P s -> Q s.

(** Quantification. *)

Definition aexists {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => exists (a: A), P a s.

Definition aforall {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => forall (a: A), P a s.

(** A few notations to improve legibility. *)

Notation "P -->> Q" := (aimp P Q) (at level 95, no associativity).
Notation "P //\\ Q" := (aand P Q) (at level 80, right associativity).
Notation "P \\// Q" := (aor P Q) (at level 75, right associativity).

(** ** 2.2.  The rules of Hoare logic *)

(** Here are the base rules for weak Hoare logic.
    They define a relation [ ⦃P⦄ c ⦃Q⦄], where
-   [P] is the precondition, assumed to hold "before" executing [c];
-   [c] is the program or program fragment we reason about;
-   [Q] is the postcondition, guaranteed to hold "after" executing [c].

  This is a "weak" logic, meaning that it does not guarantee termination
  of the command [c].  What is guaranteed is that if [c] terminates,
  then its final store satisfies postcondition [Q]. *)

Reserved Notation "⦃ P ⦄ c ⦃ Q ⦄" (at level 90, c at next level).

Inductive Hoare: assertion -> com -> assertion -> Prop :=
  | Hoare_skip: forall P,
      ⦃ P ⦄ SKIP ⦃ P ⦄
  | Hoare_assign: forall P x a,
      ⦃ aupdate x a P ⦄ ASSIGN x a ⦃ P ⦄
  | Hoare_seq: forall P Q R c1 c2,
      ⦃ P ⦄ c1 ⦃ Q ⦄ ->
      ⦃ Q ⦄ c2 ⦃ R ⦄ ->
      ⦃ P ⦄ c1;;c2 ⦃ R ⦄
  | Hoare_ifthenelse: forall P Q b c1 c2,
      ⦃ atrue b //\\ P ⦄ c1 ⦃ Q ⦄ ->
      ⦃ afalse b //\\ P ⦄ c2 ⦃ Q ⦄ ->
      ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄
  | Hoare_while: forall P b c,
      ⦃ atrue b //\\ P ⦄ c ⦃ P ⦄ ->
      ⦃ P ⦄ WHILE b c ⦃ afalse b //\\ P ⦄
  | Hoare_havoc: forall x Q,
      ⦃ aforall (fun n => aupdate x (CONST n) Q) ⦄ HAVOC x ⦃ Q ⦄
  | Hoare_assert: forall P b,
      ⦃ atrue b //\\ P ⦄ ASSERT b ⦃ atrue b //\\ P ⦄
  | Hoare_consequence: forall P Q P' Q' c,
      ⦃ P ⦄ c ⦃ Q ⦄ ->
      P' -->> P ->
      Q -->> Q' ->
      ⦃ P' ⦄ c ⦃ Q' ⦄

where "⦃ P ⦄ c ⦃ Q ⦄" := (Hoare P c Q).

(** Here are the rules for strong Hoare logic, defining strong triples
    [ 〚P〛 c 〚Q〛 ] that guarantee that [c] terminates.
    The only difference with weak triples is the rule for [while] loops. *)

Reserved Notation "〚 P 〛 c 〚 Q 〛" (at level 90, c at next level).

Definition alessthan (a: aexp) (v: int) : assertion :=
  fun s => 0 <= aeval a s < v.

Inductive HOARE: assertion -> com -> assertion -> Prop :=
  | HOARE_skip: forall P,
      〚 P 〛 SKIP 〚 P 〛
  | HOARE_assign: forall P x a,
      〚 aupdate x a P 〛 ASSIGN x a 〚 P 〛
  | HOARE_seq: forall P Q R c1 c2,
      〚 P 〛 c1 〚 Q 〛 ->
      〚 Q 〛 c2 〚 R 〛 ->
      〚 P 〛 c1;;c2 〚 R 〛
  | HOARE_ifthenelse: forall P Q b c1 c2,
      〚 atrue b //\\ P 〛 c1 〚 Q 〛 ->
      〚 afalse b //\\ P 〛 c2 〚 Q 〛 ->
      〚 P 〛 IFTHENELSE b c1 c2 〚 Q 〛
  | HOARE_while: forall P b c a,
      (forall v,
         〚 atrue b //\\ aequal a v //\\ P 〛 c 〚 alessthan a v //\\ P 〛) ->
      〚 P 〛 WHILE b c 〚 afalse b //\\ P 〛
  | HOARE_havoc: forall x Q,
      〚 aforall (fun n => aupdate x (CONST n) Q) 〛 HAVOC x 〚 Q 〛
  | HOARE_assert: forall P b,
      〚 atrue b //\\ P 〛 ASSERT b 〚 atrue b //\\ P 〛
  | HOARE_consequence: forall P Q P' Q' c,
      〚 P 〛 c 〚 Q 〛 ->
      P' -->> P ->
      Q -->> Q' ->
      〚 P' 〛 c 〚 Q' 〛

where "〚 P 〛 c 〚 Q 〛" := (HOARE P c Q).

(** ** 2.3. Derived and admissible rules *)

Lemma Hoare_consequence_pre: forall P P' Q c,
      ⦃ P ⦄ c ⦃ Q ⦄ ->
      P' -->> P ->
      ⦃ P' ⦄ c ⦃ Q ⦄.
Proof.
move=>???? H ?.
by apply: Hoare_consequence; first by exact: H.
Qed.

Lemma Hoare_consequence_post: forall P Q Q' c,
      ⦃ P ⦄ c ⦃ Q ⦄ ->
      Q -->> Q' ->
      ⦃ P ⦄ c ⦃ Q' ⦄.
Proof.
move=>???? H ?.
by apply: Hoare_consequence; first by exact: H.
Qed.

Lemma Floyd_assign: forall P x a,
  ⦃ P ⦄ ASSIGN x a ⦃ aexists (fun x0 => aexists (fun v =>
                          aequal (VAR x) v //\\
                          aupdate x (CONST x0) (P //\\ aequal a v))) ⦄.
Proof.
move=>? x a.
apply: Hoare_consequence_pre; first by apply: Hoare_assign.
move=>s Ps.
set (x0 := s x).
set (v := aeval a s).
set (s' := update x v s).
set (s'' := update x x0 s').
have EQ: (s'' = s).
- apply: functional_extensionality=>?.
  rewrite /s'' /s' /x0 /update.
  by case: eqP=>//->.
rewrite /aupdate. exists x0, v; split=>/=.
- by apply: update_same.
by rewrite -/v -/s' -/s'' EQ; split.
Qed.

(** Some derived constructs, with proof rules. *)

Lemma Hoare_ifthen: forall b c P Q,
    ⦃ atrue b //\\ P ⦄ c ⦃ Q ⦄ ->
    afalse b //\\ P -->> Q ->
    ⦃ P ⦄ IFTHENELSE b c SKIP ⦃ Q ⦄.
Proof.
move=>????? H.
apply: Hoare_ifthenelse=>//.
apply/Hoare_consequence_pre/H.
by exact: Hoare_skip.
Qed.

Definition DOWHILE (c: com) (b: bexp) : com :=
  c ;; WHILE b c.

Lemma Hoare_dowhile: forall P b c Q,
  ⦃ P ⦄ c ⦃ Q ⦄ -> (atrue b //\\ Q -->> P) ->
  ⦃ P ⦄ DOWHILE c b ⦃ afalse b //\\ Q ⦄.
Proof.
move=>???? H ?.
apply: Hoare_seq; first by exact: H.
by apply/Hoare_while/Hoare_consequence_pre; first by exact: H.
Qed.

(** A frame rule for strong triples.  Used to reason about "for" loops below. *)

Fixpoint assigns (c: com) (x: ident) : bool :=
  match c with
  | SKIP => false
  | ASSIGN y a => x == y
  | SEQ c1 c2 => assigns c1 x || assigns c2 x
  | IFTHENELSE b c1 c2 => assigns c1 x || assigns c2 x
  | WHILE b c => assigns c x
  | ASSERT b => false
  | HAVOC y => x == y
  end.

Definition independent (A: assertion) (vars: ident -> Prop) : Prop :=
  forall (s1 s2: store),
  (forall x, ~ vars x -> s1 x = s2 x) ->
  A s1 -> A s2.

(*
Ltac Tauto :=
  let s := fresh "s" in
  unfold aand, aor, aimp in *;
  intro s;
  repeat (match goal with [ H: (forall (s': store), _) |- _ ] => specialize (H s) end);
  intuition auto.
*)

Lemma HOARE_frame:
  forall R P c Q,
  〚 P 〛 c 〚 Q 〛 ->
  independent R (assigns c) ->
  〚 P //\\ R 〛 c 〚 Q //\\ R 〛.
Proof.
move=>R ???.
have IND_SUB: forall (vars1 vars2: ident -> Prop),
              independent R vars1 ->
              (forall x, vars2 x -> vars1 x) ->
              independent R vars2.
- rewrite /independent=>?? H H0 ?? HE.
  apply/H=>? H1; apply/HE; move: H1.
  by apply/contra_not/H0.
elim=>/=.
- by move=>??; apply: HOARE_skip.
- move=>P ?? IND.
  apply: (@HOARE_consequence _ (P //\\ R)); first by [apply: HOARE_assign]; last by [].
  rewrite /aupdate=>? [? B]; split=>//.
  apply/IND/B=>??.
  by rewrite update_other // => /eqP; rewrite eq_sym.
- move=>? Q ???? IH1 ? IH2 HR.
  apply: (@HOARE_seq _ (Q //\\ R)).
  - apply/IH1/(@IND_SUB _ _ HR)=>??.
    by apply/orP; left.
  apply/IH2/(@IND_SUB _ _ HR)=>??.
  by apply/orP; right.
- move=>? Q ???? IH1 ? IH2 HR.
  apply: HOARE_ifthenelse; (apply: (@HOARE_consequence _ (Q //\\ R)); last by []).
  - by apply/IH1/(@IND_SUB _ _ HR)=>??; apply/orP; left.
  - by move=>? /and_assoc.
  - by apply/IH2/(@IND_SUB _ _ HR)=>??; apply/orP; right.
  - by move=>? /and_assoc.
- move=>P ?? a ? H ?.
  apply: (@HOARE_consequence (P //\\ R)); try by [].
  - apply: (@HOARE_while _ _ _ a) =>?.
    apply: HOARE_consequence; first by [apply: H].
    - by move=>?[?][?][?].
    by move=>? /and_assoc.
  by move=>? /and_assoc.
- move=>? Q IND.
  apply: (@HOARE_consequence _ (Q //\\ R)); last by [].
  - by apply: HOARE_havoc.
  move=>? [AQ Rs] n; split; first by exact: AQ.
  apply/IND/Rs=>??.
  by rewrite update_other // => /eqP; rewrite eq_sym.
- move=>P ??.
  by apply: HOARE_consequence; first by [exact: (@HOARE_assert (P //\\ R))]; move=>? /and_assoc.
- move=>?????? IH HP HQ ?.
  by apply: HOARE_consequence; first by [apply: IH]; move=>?[??]; split=>//; [apply: HP| apply: HQ].
Qed.

(** A counted "for" loop. *)

Definition FOR (i: ident) (l: aexp) (h: ident) (c: com) : com :=
  ASSIGN i l;;
  WHILE (LESSEQUAL (VAR i) (VAR h)) (c ;; ASSIGN i (PLUS (VAR i) (CONST 1))).

Lemma HOARE_for: forall l h i c P,
  〚 atrue (LESSEQUAL (VAR i) (VAR h)) //\\ P 〛
    c
  〚 aupdate i (PLUS (VAR i) (CONST 1)) P 〛 ->
  ~assigns c i -> ~assigns c h -> i <> h ->
  〚 aupdate i l P 〛 FOR i l h c 〚 afalse (LESSEQUAL (VAR i) (VAR h)) //\\ P 〛.
Proof.
move=>? h i ? P H ???.
apply: (@HOARE_seq _ P); first by apply: HOARE_assign.
set (variant := PLUS (MINUS (VAR h) (VAR i)) (CONST 1)).
apply: (@HOARE_while _ _ _ variant)=>v.
apply: HOARE_seq.
- apply: HOARE_consequence.
  - apply: (@HOARE_frame (aequal variant v //\\ atrue (LESSEQUAL (VAR i) (VAR h)))); first by exact: H.
    by move=>?? E; rewrite /aequal /atrue /aand /= !E.
  - by move=>?[?][?]?.
  by move=>? A; exact: A.
apply: (@HOARE_consequence _ (alessthan variant v //\\ P)); first by [exact: HOARE_assign]; try by [].
move=>?[A][B]C; rewrite /aequal /= in B; rewrite /atrue /= in C.
split=>//=.
by rewrite /alessthan /variant /= update_same update_other //; lia.
Qed.

(** Some inversion lemmas. *)

Lemma Hoare_skip_inv: forall P Q,
  ⦃ P ⦄ SKIP ⦃ Q ⦄ -> (P -->> Q).
Proof.
move=>?? H.
elim: _ {-1}_ _ /H (erefl SKIP)=>//.
- by move=>? _.
- move=>?????? IH H1 H2 ???.
  by apply/H2/IH/H1.
Qed.

Lemma Hoare_assign_inv: forall x a P Q,
  ⦃ P ⦄ ASSIGN x a ⦃ Q ⦄ -> (P -->> aupdate x a Q).
Proof.
move=>x a ?? H.
elim: _ {-1}_ _ /H (erefl (ASSIGN x a))=>//.
- by move=>???; case=>->->.
- move=>?????? IH H1 H2 ???.
  by apply/H2/IH/H1.
Qed.

Lemma Hoare_seq_inv: forall c1 c2 P Q,
  ⦃ P ⦄ c1 ;; c2 ⦃ Q ⦄ ->
  exists R, ⦃ P ⦄ c1 ⦃ R ⦄ /\ ⦃ R ⦄ c2 ⦃ Q ⦄.
Proof.
move=>c1 c2 ?? H.
elim: _ {-1}_ _ /H (erefl (c1;; c2))=>//.
- move=>? Q2 ???????; case=>->->.
  by exists Q2.
- move=>?????? IH H1 H2 ?; case: IH=>// R[C1]C2.
  exists R; split.
  - by apply/Hoare_consequence_pre/H1.
  by apply/Hoare_consequence_post/H2.
Qed.

Lemma Hoare_ifthenelse_inv: forall b c1 c2 P Q,
  ⦃ P ⦄ IFTHENELSE b c1 c2 ⦃ Q ⦄ ->
  ⦃ atrue b //\\ P ⦄ c1 ⦃ Q ⦄ /\ ⦃ afalse b //\\ P ⦄ c2 ⦃ Q ⦄.
Proof.
move=>b c1 c2 ?? H.
elim: _ {-1}_ _ /H (erefl (IFTHENELSE b c1 c2))=>//.
- by move=>?????????; case=>->->->.
- move=>?????? IH H1 H2 ?; case: IH=>// C1 C2.
  split; apply/Hoare_consequence/H2.
  - by exact: C1.
  - by move=>?[?]?; split=>//; apply: H1.
  - by exact: C2.
  - by move=>?[?]?; split=>//; apply: H1.
Qed.

Lemma Hoare_while_inv: forall b c P Q,
  ⦃ P ⦄ WHILE b c ⦃ Q ⦄ ->
  exists Inv, ⦃ atrue b //\\ Inv ⦄ c ⦃ Inv ⦄
           /\ (P -->> Inv) /\ (afalse b //\\ Inv -->> Q).
Proof.
move=>b c ?? H.
elim: _ {-1}_ _ /H (erefl (WHILE b c))=>//.
- move=>R ????; case=>->->.
  by exists R; do 2!split=>//.
- move=>?????? IH H1 H2 ?.
  case: IH=>// Inv [C][X]Y.
  by exists Inv; split=>//; split=>?; [move/H1/X|move/Y/H2].
Qed.

Lemma Hoare_havoc_inv: forall x P Q,
  ⦃ P ⦄ HAVOC x ⦃ Q ⦄ -> (P -->> aforall (fun n => aupdate x (CONST n) Q)).
Proof.
move=>x ?? H.
elim: _ {-1}_ _ /H (erefl (HAVOC x))=>//.
- by move=>??; case=>->.
- move=>?????? IH H1 H2 ????.
  by apply/H2/IH/H1.
Qed.

Lemma Hoare_assert_inv: forall b P Q,
  ⦃ P ⦄ ASSERT b ⦃ Q ⦄ ->
  exists R, (P -->> atrue b //\\ R) /\ (atrue b //\\ R -->> Q).
Proof.
move=>b ?? H.
elim: _ {-1}_ _ /H (erefl (ASSERT b)) =>//.
- move=>R ?; case=>->.
  by exists R; split.
- move=>?????? IH H1 H2 ?.
  case: IH=>// R [A B].
  by exists R; split=>?; [move/H1/A|move/B/H2].
Qed.

(** Some admissible rules. *)

Lemma Hoare_conj:
  forall c P1 P2 Q1 Q2,
  ⦃ P1 ⦄ c ⦃ Q1 ⦄ -> ⦃ P2 ⦄ c ⦃ Q2 ⦄ ->
  ⦃ P1 //\\ P2 ⦄ c ⦃ Q1 //\\ Q2 ⦄.
Proof.
elim.
- move=>???? H1 H2.
  move/Hoare_skip_inv: H1=>H1; move/Hoare_skip_inv: H2=>H2.
  apply: Hoare_consequence_post; first by exact: Hoare_skip.
  by move=>?[?]?; split; [apply:H1|apply:H2].
- move=>?????? H1 H2.
  move/Hoare_assign_inv: H1=>H1; move/Hoare_assign_inv: H2=>H2.
  apply: Hoare_consequence_pre; first by exact: Hoare_assign.
  by move=>?[?]?; split; [apply:H1|apply:H2].
- move=>? IH1 ? IH2 ???? H1 H2.
  move/Hoare_seq_inv: H1=>[R1 [??]].
  move/Hoare_seq_inv: H2=>[R2 [??]].
  by apply: (@Hoare_seq _ (R1 //\\ R2)); [apply: IH1| apply: IH2].
- move=>?? IH1 ? IH2 ???? H1 H2.
  move/Hoare_ifthenelse_inv: H1=>[C11 C21].
  move/Hoare_ifthenelse_inv: H2=>[C12 C22].
  apply: Hoare_ifthenelse; apply: Hoare_consequence_pre.
  - by apply/IH1/C12/C11.
  - by move=>?[?][?]?.
  - by apply/IH2/C22/C21.
  - by move=>?[?][?]?.
- move=>?? IH ???? H1 H2.
  move/Hoare_while_inv: H1=>[Inv1][C1][A1]B1.
  move/Hoare_while_inv: H2=>[Inv2][C2][A2]B2.
  apply: (@Hoare_consequence (Inv1 //\\ Inv2)).
  - apply/Hoare_while/Hoare_consequence_pre.
    - by apply/IH/C2/C1.
    by move=>?[?][?]?.
  - by move=>?[?]?; split; [apply:A1|apply:A2].
  by move=>?[?][?]?; split; [apply:B1|apply:B2].
- move=>????? H1 H2.
  move/Hoare_assert_inv: H1=>[R1][A1]B1.
  move/Hoare_assert_inv: H2=>[R2][A2]B2.
  apply: Hoare_consequence; first by exact: (@Hoare_assert (R1 //\\ R2)).
  - by move=>?[] /A1 [?]? /A2 [].
  by move=>?[?][?]?; split; [apply:B1|apply:B2].
move=>????? H1 H2.
move/Hoare_havoc_inv: H1=>H1; move/Hoare_havoc_inv: H2=>H2.
apply: Hoare_consequence_pre; first by exact: Hoare_havoc.
by move=>?[?]?; rewrite /aforall /aupdate=>?; split; [apply: H1|apply: H2].
Qed.

Lemma Hoare_disj:
  forall c P1 P2 Q1 Q2,
  ⦃ P1 ⦄ c ⦃ Q1 ⦄ -> ⦃ P2 ⦄ c ⦃ Q2 ⦄ ->
  ⦃ P1 \\// P2 ⦄ c ⦃ Q1 \\// Q2 ⦄.
Proof.
elim.
- move=>???? H1 H2.
  move/Hoare_skip_inv: H1=>H1; move/Hoare_skip_inv: H2=>H2.
  apply: Hoare_consequence_post; first by exact: Hoare_skip.
  by move=>?; case; [left; apply:H1|right; apply:H2].
- move=>?????? H1 H2.
  move/Hoare_assign_inv: H1=>H1; move/Hoare_assign_inv: H2=>H2.
  apply: Hoare_consequence_pre; first by exact: Hoare_assign.
  by move=>?; case; [left; apply:H1|right; apply:H2].
- move=>? IH1 ? IH2 ???? H1 H2.
  move/Hoare_seq_inv: H1=>[R1 [??]].
  move/Hoare_seq_inv: H2=>[R2 [??]].
  by apply: (@Hoare_seq _ (R1 \\// R2)); [apply: IH1| apply: IH2].
- move=>?? IH1 ? IH2 ???? H1 H2.
  move/Hoare_ifthenelse_inv: H1=>[C11 C21].
  move/Hoare_ifthenelse_inv: H2=>[C12 C22].
  apply: Hoare_ifthenelse; apply: Hoare_consequence_pre.
  - by apply/IH1/C12/C11.
  - by move=>?[?]; case; [left|right].
  - by apply/IH2/C22/C21.
  - by move=>?[?]; case; [left|right].
- move=>?? IH ???? H1 H2.
  move/Hoare_while_inv: H1=>[Inv1][C1][A1]B1.
  move/Hoare_while_inv: H2=>[Inv2][C2][A2]B2.
  apply: (@Hoare_consequence (Inv1 \\// Inv2)).
  - apply/Hoare_while/Hoare_consequence_pre.
    - by apply/IH/C2/C1.
    by move=>?[?]; case; [left|right].
  - by move=>?; case; [left; apply:A1|right; apply:A2].
  by move=>?[?]; case; [left; apply:B1|right; apply:B2].
- move=>????? H1 H2.
  move/Hoare_assert_inv: H1=>[R1][A1]B1.
  move/Hoare_assert_inv: H2=>[R2][A2]B2.
  apply: Hoare_consequence; first by exact: (@Hoare_assert (R1 \\// R2)).
  - by move=>?; case; [move/A1|move/A2]; case=>??; split=>//; [left|right].
  by move=>?[?]; case=>?; [left; apply:B1|right; apply:B2].
move=>????? H1 H2.
move/Hoare_havoc_inv: H1=>H1; move/Hoare_havoc_inv: H2=>H2.
apply: Hoare_consequence_pre; first by exact: Hoare_havoc.
by move=>?; case=>?; rewrite /aforall /aupdate=>?; [left; apply: H1|right; apply: H2].
Qed.

Definition choice_axiom :=
  forall (A B: Type) (R: A -> B -> Prop),
  (forall a, exists b, R a b) ->
  exists f: A -> B, forall a, R a (f a).

Lemma Hoare_exists:
  choice_axiom ->
  forall (X: Type) c (P Q: X -> assertion),
  (forall x, ⦃ P x ⦄ c ⦃ Q x ⦄) ->
  ⦃ aexists P ⦄ c ⦃ aexists Q ⦄.
Proof.
move=>CHOICE X; elim.
- move=>?? H.
  apply: Hoare_consequence_pre; first by exact: Hoare_skip.
  by move=>?[x ?]; exists x; apply: Hoare_skip_inv; first by apply: H.
- move=>???? H.
  apply: Hoare_consequence_pre; first by exact: Hoare_assign.
  by move=>?[x ?]; exists x; apply: Hoare_assign_inv; first by apply: H.
- move=>c1 IH1 c2 IH2 P Q ?.
  set (REL := fun (x : X) (R: assertion) => Hoare (P x) c1 R /\ Hoare R c2 (Q x)).
  have [R H']: exists R: X -> assertion, forall x: X, REL x (R x)
   by apply: CHOICE=>?; apply: Hoare_seq_inv.
  by apply: (@Hoare_seq _ (aexists R)); [apply: IH1|apply: IH2]=>y; case: (H' y).
- move=>b c1 IH1 c2 IH2 P Q H.
  have H1: Hoare (aexists (fun x => atrue b //\\ P x)) c1 (aexists Q)
    by apply: IH1=>y; case: (Hoare_ifthenelse_inv _ _ _ _ _ (H y)).
  have H2: Hoare (aexists (fun x => afalse b //\\ P x)) c2 (aexists Q)
    by apply: IH2=>y; case: (Hoare_ifthenelse_inv _ _ _ _ _ (H y)).
  by apply: Hoare_ifthenelse; apply: Hoare_consequence_pre;
  [apply: H1| |apply: H2|]=>?[?][x ?]; exists x.
- move=>b c IH P Q ?.
  set REL := fun (x : X) (Inv: assertion) =>
    Hoare (atrue b //\\ Inv) c Inv /\ (P x -->> Inv) /\ (afalse b //\\ Inv -->> Q x).
  have [Inv H']: exists Inv: X -> assertion, forall x: X, REL x (Inv x)
    by apply: CHOICE=>?; apply: Hoare_while_inv.
  apply: (@Hoare_consequence (aexists Inv)).
  - apply: Hoare_while.
    apply: (@Hoare_consequence_pre (aexists (fun x => atrue b //\\ Inv x))).
    - by apply: IH=>x; case: (H' x).
    by move=>?[?][x ?]; exists x.
  - by move=>?[x ?]; exists x; case: (H' x)=>_ [HP] _; apply: HP.
  by move=>?[?][x ?]; exists x; case: (H' x)=>_[_]; apply.
- move=>b P Q ?.
  set REL := fun (x : X) (R: assertion) =>
                (P x -->> atrue b //\\ R) /\ (atrue b //\\ R -->> Q x).
  have [R A]: exists R: X -> assertion, forall x: X, REL x (R x)
    by apply: CHOICE=>?; apply: Hoare_assert_inv.
  apply: Hoare_consequence; first by apply: (@Hoare_assert (aexists R)).
  - move=>?[x Px]; move: (A x)=>[B ?]; case: (B _ Px)=>??; split=>//.
    by exists x.
  by move=>?[?][x ?]; exists x; case: (A x)=>[_]; apply.
- move=>??? H.
  apply: Hoare_consequence_pre; first by exact: Hoare_havoc.
  by move=>?[x ?]?; exists x; apply: Hoare_havoc_inv; first by exact: H.
Qed.

Lemma Hoare_forall:
  choice_axiom ->
  forall (X: Type) (inhabited: X) c (P Q: X -> assertion),
  (forall x, ⦃ P x ⦄ c ⦃ Q x ⦄) ->
  ⦃ aforall P ⦄ c ⦃ aforall Q ⦄.
Proof.
move=>CHOICE X inhabited; elim.
- move=>?? H.
  apply: Hoare_consequence_pre; first by exact: Hoare_skip.
  by move=>???; apply: Hoare_skip_inv; first by apply: H.
- move=>???? H.
  apply: Hoare_consequence_pre; first by exact: Hoare_assign.
  by move=>???; apply: Hoare_assign_inv; first by apply: H.
- move=>c1 IH1 c2 IH2 P Q ?.
  set REL := fun (x : X) (R: assertion) => Hoare (P x) c1 R /\ Hoare R c2 (Q x).
  have [R H']: exists R: X -> assertion, forall x: X, REL x (R x)
   by apply: CHOICE=>?; apply: Hoare_seq_inv.
  by apply: (@Hoare_seq _ (aforall R)); [apply: IH1|apply: IH2]=>y; case: (H' y).
- move=>b c1 IH1 c2 IH2 P Q H.
  have H1: Hoare (aforall (fun x => atrue b //\\ P x)) c1 (aforall Q)
    by apply: IH1=>y; case: (Hoare_ifthenelse_inv _ _ _ _ _ (H y)).
  have H2: Hoare (aforall (fun x => afalse b //\\ P x)) c2 (aforall Q)
    by apply: IH2=>y; case: (Hoare_ifthenelse_inv _ _ _ _ _ (H y)).
  by apply: Hoare_ifthenelse; apply: Hoare_consequence_pre;
  [apply: H1| |apply: H2|]=>?[??]?.
- move=>b c IH P Q ?.
  set REL := fun (x : X) (Inv: assertion) =>
    Hoare (atrue b //\\ Inv) c Inv /\ (P x -->> Inv) /\ (afalse b //\\ Inv -->> Q x).
  have [Inv H']: exists Inv: X -> assertion, forall x: X, REL x (Inv x)
    by apply: CHOICE=>?; apply: Hoare_while_inv.
  apply: (@Hoare_consequence (aforall Inv)).
  - apply: Hoare_while.
    apply: (@Hoare_consequence_pre (aforall (fun x => atrue b //\\ Inv x))).
    - by apply: IH=>x; case: (H' x).
    by move=>?[??]?.
  - by move=>?? x; case: (H' x) =>_ [HP] _; apply: HP.
  by move=>?[??]x; case: (H' x)=>_[_]; apply.
- move=>b P Q ?.
  set REL := fun (x : X) (R: assertion) =>
                (P x -->> atrue b //\\ R) /\ (atrue b //\\ R -->> Q x).
  have [R A]: exists R: X -> assertion, forall x: X, REL x (R x)
    by apply: CHOICE=>?; apply: Hoare_assert_inv.
  apply: Hoare_consequence; first by apply: (@Hoare_assert (aforall R)).
  - move=>? Px; move: (A inhabited)=>[B ?]; case: (B _ (Px inhabited))=>??; split=>// x.
    by move: (A x)=>[Bx ?]; case: (Bx _ (Px x)).
  by move=>?[??]x; case: (A x)=>[_]; apply.
- move=>??? H.
  apply: Hoare_consequence_pre; first by exact: Hoare_havoc.
  by move=>????; apply: Hoare_havoc_inv; first by exact: H.
Qed.

(** ** 2.4. Soundness *)

(** *** Soundness of Hoare logic, in the style of type soundness proofs. *)

Module Soundness1.

Lemma Hoare_safe:
  forall P c Q,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  forall s, P s -> ~error c s.
Proof.
move=>???; elim=>//=; try by move=>*.
- by move=>??? [A ?] H; rewrite A in H.
- by move=>?????? H HP ??? HE; apply/H/HE/HP.
Qed.

Lemma Hoare_step:
  forall P c Q,
  ⦃ P ⦄ c ⦃ Q ⦄ ->
  forall s c' s',
  P s -> red (c, s) (c', s') -> exists P', ⦃ P' ⦄ c' ⦃ Q ⦄ /\ P' s'.
Proof.
move=>???; elim.
- move=>? s c' s' ? R.
  by case: {-2}_ {-1}_ / R (erefl (SKIP, s)) (erefl (c', s')).
- move=>P x a s c' s' ? R.
  case: {-2}_ {-1}_ / R (erefl (ASSIGN x a, s)) (erefl (c', s'))=>// ???; case=>->->->; case=>->->.
  by exists P; split=>//; exact: Hoare_skip.
- move=>? Q ? c1 c2 H IH1 ?? s c' s' Ps R.
  case: {-2}_ {-1}_ / R (erefl (c1;; c2, s)) (erefl (c', s'))=>//.
  - move=>??; case=>EC ->->; case=>->->; rewrite -{}EC in H.
    exists Q; split=>//.
    by apply: Hoare_skip_inv; first by exact: H.
  - move=>????? R; case=>E1 E2 ES; case=>->->; rewrite {}E1 {}E2 {}ES in R *.
    move: (IH1 _ _ _ Ps R)=>[P'][HO' Ps'].
    by exists P'; split=>//; apply: Hoare_seq; first by exact: HO'.
- move=>P ? b c1 c2 ???? s c' s' ? R.
  case: {-2}_ {-1}_ / R (erefl (IFTHENELSE b c1 c2, s)) (erefl (c', s'))=>// ????.
  case=>->->->->; case=>->->.
  exists (if beval b s then atrue b //\\ P else afalse b //\\ P).
  by split; case/boolP: (beval _ _).
- move=>P b c1 H ? s c' s' ? R.
  case: {-2}_ {-1}_ / R (erefl (WHILE b c1, s)) (erefl (c', s'))=>// ??? HB.
  - case=>EB _ ES; case=>->->; rewrite {}EB {}ES in HB *.
    by exists (afalse b //\\ P); split=>//; exact: Hoare_skip.
  - case=>EB -> ES; case=>->->; rewrite {}EB {}ES in HB *.
  exists (atrue b //\\ P); split=>//; apply: Hoare_seq; first by exact: H.
  by apply: Hoare_while.
- move=>x Q s c' s' H R.
  case: {-2}_ {-1}_ / R (erefl (HAVOC x, s)) (erefl (c', s'))=>// ???.
  case=>->->; case=>->->.
  by exists Q; split; [exact: Hoare_skip | apply: H].
- move=>P b s c' s' [??] R.
  case: {-2}_ {-1}_ / R (erefl (ASSERT b, s)) (erefl (c', s'))=>// ?? HB.
  case=>EB ES; case=>->->; rewrite {}EB {}ES in HB *.
  by exists (atrue b //\\ P); split=>//; exact: Hoare_skip.
- move=>?????? IH H1 ???? Ps R.
  move/H1: Ps=>Ps; case: (IH _ _ _ Ps R)=>R' [H0 ?].
  exists R'; split=>//.
  by apply: Hoare_consequence_post; first by exact H0.
Qed.

Corollary Hoare_steps:
  forall P Q c s c' s',
  ⦃ P ⦄ c ⦃ Q ⦄ -> P s -> star red (c, s) (c', s') ->
  exists P', ⦃ P' ⦄ c' ⦃ Q ⦄ /\ P' s'.
Proof.
have REC: forall cs cs', star red cs cs' ->
          forall P Q, Hoare P cs.1 Q -> P cs.2 ->
          exists P', Hoare P' cs'.1 Q /\ P' cs'.2.
- move=>??; elim.
  - by move=>? P ???; exists P.
  - move=>[??][??][??] R ? /= IH ?? H1 H2.
    case: (Hoare_step _ _ _ H1 _ _ _ H2 R)=>? [HO ?].
    by apply: IH; first by exact: HO.
by move=>?? c s c' s' H ??; apply: (REC (c,s) (c',s'))=>//; first by exact: H.
Qed.

Corollary Hoare_sound:
  forall P c Q s,
  ⦃ P ⦄ c ⦃ Q ⦄ -> P s ->
  ~ goeswrong c s /\ (forall s', terminates c s s' -> Q s').
Proof.
move=>???? HO Ps; split.
- move=>[?][?][RED STUCK].
  case: (Hoare_steps _ _ _ _ _ _ HO Ps RED)=>? [HO' Ps'].
  by apply: Hoare_safe; [exact: HO'| exact: Ps'|].
- move=>?[?][RED TERM]; rewrite TERM in RED.
  case: (Hoare_steps _ _ _ _ _ _ HO Ps RED)=>? [HO' Ps'].
  by apply: Hoare_skip_inv; first by exact: HO'.
Qed.

End Soundness1.

(** *** Soundness of strong Hoare logic, using an inductive "safe" predicate. *)

Module Soundness2.

Inductive safe (Q: assertion): com -> store -> Prop :=
  | safe_now: forall c s,
      terminated c -> Q s ->
      safe Q c s
  | safe_step: forall c s,
      ~terminated c -> ~error c s ->
      (forall c' s', red (c, s) (c', s') -> safe Q c' s') ->
      safe Q c s.

Definition Triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s, P s -> safe Q c s.

Notation "〚〚 P 〛〛 c 〚〚 Q 〛〛" := (Triple P c Q) (at level 90, c at next level).

Lemma Triple_skip: forall P,
      〚〚 P 〛〛 SKIP 〚〚 P 〛〛.
Proof.
by move=>???; apply: safe_now.
Qed.

Lemma Triple_assign: forall P x a,
      〚〚 aupdate x a P 〛〛 ASSIGN x a 〚〚 P 〛〛.
Proof.
move=>? x a s ?; apply: safe_step=>// c' s' R.
case: {-2}_ {-1}_ / R (erefl (ASSIGN x a, s)) (erefl (c', s'))=>// ???.
case=>->->->; case=>->->.
by apply: safe_now.
Qed.

Remark safe_seq:
  forall (Q R: assertion) (c': com),
  (forall s, Q s -> safe R c' s) ->
  forall c s, safe Q c s -> safe R (c ;; c') s.
Proof.
move=>?? c H ??; elim=>c0 s.
- move=>-> ?; apply: safe_step=>// c' s' R.
  case: {-2}_ {-1}_ / R (erefl (SKIP;; c, s)) (erefl (c', s'))=>//.
  - move=>??; case=>->->; case=>->->.
    by apply: H.
  - move=>??? c2 s2 R; case=>E2 -> E1; case=>->->; rewrite {}E1 {}E2 in R.
    by case: {-2}_ {-1}_ / R (erefl (SKIP, s)) (erefl (c2, s2)).
move=>HT ?? H2; apply: safe_step=>// c' s' R.
case: {-1}_ {-1}_ / R (erefl (c0;; c, s)) (erefl (c', s'))=>//.
- by move=>??; case=>E0; rewrite E0 /terminated in HT.
- move=>????? R; case=>EC <- ES; case=>->->; rewrite -{}EC -{}ES in R.
  by apply: H2.
Qed.

Lemma Triple_seq: forall P Q R c1 c2,
      〚〚 P 〛〛 c1 〚〚 Q 〛〛 -> 〚〚 Q 〛〛 c2 〚〚 R 〛〛 ->
      〚〚 P 〛〛 c1;;c2 〚〚 R 〛〛.
Proof.
move=>????? H H2 ??; apply: safe_seq; first by exact: H2.
by apply: H.
Qed.

Lemma Triple_ifthenelse: forall P Q b c1 c2,
      〚〚 atrue b //\\ P 〛〛 c1 〚〚 Q 〛〛 ->
      〚〚 afalse b //\\ P 〛〛 c2 〚〚 Q 〛〛 ->
      〚〚 P 〛〛 IFTHENELSE b c1 c2 〚〚 Q 〛〛.
Proof.
move=>?? b c1 c2 H1 H2 s ?; apply: safe_step=>// c' s' R.
case: {-2}_ {-1}_ / R (erefl (IFTHENELSE b c1 c2, s)) (erefl (c', s'))=>// ????.
case=>->->->->; case=>->->.
by case/boolP: (beval _ _)=>?; [apply: H1 | apply: H2].
Qed.

Lemma Triple_while: forall P variant b c,
  (forall v,
     〚〚 atrue b //\\ aequal variant v //\\ P 〛〛
     c
     〚〚 alessthan variant v //\\ P 〛〛)
  ->
     〚〚 P 〛〛 WHILE b c 〚〚 afalse b //\\ P 〛〛.
Proof.
move=>P var b c H.
have REC: forall v s, P s -> aeval var s = v ->
          safe (afalse b //\\ P) (WHILE b c) s.
- apply: well_founded_induction; first by exact: well_founded_rlt.
  move=>? /= IH s ? HA; apply: safe_step=>// c' s' R.
  case: {-2}_ {-1}_ / R (erefl (WHILE b c, s)) (erefl (c', s'))=>// ??? HB.
  - case=>EB _ ES; case=>->->; rewrite {}EB {}ES in HB *.
    by apply: safe_now.
  - case=>EB -> ES; case=>->->; rewrite {}EB {}ES in HB *.
    apply: (@safe_seq (alessthan var (aeval var s) //\\ P)).
    - move=>? [P1 ?]; apply: IH=>//.
      by rewrite /alessthan HA in P1.
    by apply: H.
by move=>s ?; apply: REC.
Qed.

Lemma Triple_havoc: forall x Q,
      〚〚 aforall (fun n => aupdate x (CONST n) Q) 〛〛 HAVOC x 〚〚 Q 〛〛.
Proof.
move=>x ? s H; apply: safe_step=>// c' s' R.
case: {-2}_ {-1}_ / R (erefl (HAVOC x, s)) (erefl (c', s'))=>// ???.
case=>->->; case=>->->.
by apply: safe_now=>//; apply: H.
Qed.

Lemma Triple_assert: forall b P,
      〚〚 atrue b //\\ P 〛〛 ASSERT b 〚〚 atrue b //\\ P 〛〛.
Proof.
move=>b ? s [HA ?]; apply: safe_step=>//=; first by rewrite HA.
move=>c' s' R.
case: {-2}_ {-1}_ / R (erefl (ASSERT b, s)) (erefl (c', s'))=>// ?? HB.
case=>EB ES; case=>->->; rewrite {}EB {}ES in HB *.
by apply: safe_now.
Qed.

Lemma Triple_consequence: forall P Q P' Q' c,
      〚〚 P 〛〛 c 〚〚 Q 〛〛 -> P' -->> P -> Q -->> Q' ->
      〚〚 P' 〛〛 c 〚〚 Q' 〛〛.
Proof.
move=>? Q ? Q' ? H H1 H2 ??.
have REC: forall c s, safe Q c s -> safe Q' c s.
- move=>??; elim=>*.
  - by apply: safe_now=>//; apply: H2.
  - by apply: safe_step.
by apply/REC/H/H1.
Qed.

Theorem HOARE_sound:
  forall P c Q, 〚 P 〛 c 〚 Q 〛 -> 〚〚 P 〛〛 c 〚〚 Q 〛〛.
Proof.
move=>???; elim.
- by apply: Triple_skip.
- by apply: Triple_assign.
- by move=>?????? H ??; apply: Triple_seq; first by exact: H.
- by move=>*; apply: Triple_ifthenelse.
- by move=>*; apply: Triple_while.
- by apply: Triple_havoc.
- by move=>*; apply: Triple_assert.
- by move=>?????? H ??; apply: Triple_consequence; first by exact: H.
Qed.

End Soundness2.

(** *** Soundness of weak Hoare logic, using a coinductive "safe" predicate. *)

Module Soundness3.

Inductive safe_gen (Q : assertion) (safe : com -> store -> Prop) : com -> store -> Prop :=
| safe_now: forall c s, terminated c -> Q s -> safe_gen Q safe c s
| safe_step: forall c s, ~terminated c -> ~error c s ->
                        (forall c' s', red (c, s) (c', s') -> safe c' s') ->
                        safe_gen Q safe c s.

#[export] Hint Constructors safe_gen : core.

Lemma safe_gen_mono Q : monotone2 (safe_gen Q).
Proof.
by pmonauto.
(*
rewrite /monotone2 =>???? IN LE.
elim: IN=>??.
- by move=>??; apply: safe_now.
- by move=>?? H; apply: safe_step=>// ???; by apply/LE/H.
*)
Qed.

#[export] Hint Resolve safe_gen_mono : paco.

Definition safe Q c s := paco2 (safe_gen Q) bot2 c s.
#[export] Hint Unfold safe : core.

Lemma safe_terminated_inv: forall Q c s,
  safe Q c s -> terminated c -> Q s.
Proof.
move=>? c ? H T; punfold H.
case: {-2}_ _ / H (erefl c)=>// ?? NT ?? EC.
by rewrite EC T /terminated in NT.
Qed.

Lemma safe_not_stuck: forall Q c s,
  safe Q c s -> ~terminated c -> ~error c s.
Proof.
move=>? c ? H NT; punfold H.
case: {-2}_ _ / H (erefl c)=>// ?? T ? EC.
by rewrite EC in T; rewrite T /terminated in NT.
Qed.

Lemma safe_step_inv: forall Q c s c' s',
  safe Q c s -> red (c, s) (c', s') -> safe Q c' s'.
Proof.
move=>? c s ?? H R; punfold H.
case: {-2}_ {-2}_ / H (erefl c) (erefl s)=> ??.
- move=>T ? EC _; rewrite {}EC /terminated in T.
  rewrite {}T in R.
  by case: {-1}_ _ / R (erefl (SKIP, s)).
move=>?? S EC ES; rewrite {}EC {}ES in S.
by case: (S _ _ R).
Qed.

Definition triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s, P s -> safe Q c s.

Notation "⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄" := (triple P c Q) (at level 90, c at next level).

Lemma triple_skip: forall P,
      ⦃⦃ P ⦄⦄ SKIP ⦃⦃ P ⦄⦄.
Proof.
by move=>???; pfold; apply: safe_now.
Qed.

Lemma triple_assign: forall P x a,
      ⦃⦃ aupdate x a P ⦄⦄ ASSIGN x a ⦃⦃ P ⦄⦄.
Proof.
move=>? x a s ?; pfold; apply: safe_step=>// c' s' R.
case: {-2}_ {-1}_ / R (erefl (ASSIGN x a, s)) (erefl (c', s'))=>// ???.
case=>->->->; case=>->->; left; pfold.
by apply: safe_now.
Qed.

Remark safe_seq:
  forall (Q R: assertion) c' r,
  (forall s, Q s -> upaco2 (safe_gen R) r c' s) ->
  forall c s, safe Q c s -> paco2 (safe_gen R) r (c ;; c') s.
Proof.
move=>?? c0 ? QR.
pcofix CHR=>?? S; pfold.
punfold S. elim: S =>c1 s.
- move=>-> Qs; apply: safe_step=>// c' s' R.
  case: {-2}_ {-1}_ / R (erefl (SKIP;;c0, s)) (erefl (c', s'))=>//.
  - move=>??; case=>->->; case=>->->.
    case: (QR _ Qs)=>H; [left|right].
    - by apply: paco2_mon; first by exact: H.
    - by apply: CHR0.
  - move=>?? s1 ?? R; case=>E2; rewrite E2 in R.
    by case: {-1}_ _ / R (erefl (SKIP, s1)).
- move=>NT ? H1; apply: safe_step=>// c' s' R.
  case: {-2}_ {-1}_ / R (erefl (c1;;c0, s)) (erefl (c', s'))=>//.
  - move=>??; case=>E1.
    by rewrite -E1 /terminated in NT.
  - move=>????? R; case=>E1->E2; case=>->->; rewrite {}E1 {}E2 in R.
    by right; apply CHR; case: (H1 _ _ R).
Qed.

Remark safe_seq0:
  forall (Q R: assertion) c',
  (forall s, Q s -> safe R c' s) ->
  forall c s, safe Q c s -> safe R (c ;; c') s.
Proof.
by move=>??? H0 ?? H; apply/safe_seq/H =>??; left; apply: H0.
Qed.

Lemma triple_seq: forall P Q R c1 c2,
      ⦃⦃ P ⦄⦄ c1 ⦃⦃ Q ⦄⦄ -> ⦃⦃ Q ⦄⦄ c2 ⦃⦃ R ⦄⦄ ->
      ⦃⦃ P ⦄⦄ c1;;c2 ⦃⦃ R ⦄⦄.
Proof.
by move=>????? H ???; apply/safe_seq0/H.
Qed.

Lemma triple_while: forall P b c,
   ⦃⦃ atrue b //\\ P ⦄⦄ c ⦃⦃ P ⦄⦄ ->
   ⦃⦃ P ⦄⦄ WHILE b c ⦃⦃ afalse b //\\ P ⦄⦄.
Proof.
move=>P b c T.
have REC: forall s, P s ->
            safe (afalse b //\\ P) (WHILE b c) s.
- pcofix CHR=>s ?; pfold.
  apply: safe_step=>// c' s' R.
  case: {-2}_ {-1}_ / R (erefl (WHILE b c, s)) (erefl (c', s'))=>// ??? B.
  - case=>EB _ ES; case=>->->; rewrite {}EB {}ES in B *.
    by left; pfold; apply: safe_now.
  - case=>EB->ES; case=>->->; rewrite {}EB {}ES in B *.
    left; apply/(safe_seq P)/T=>// ??.
    by right; apply: CHR.
by move=>??; apply: REC.
Qed.

Lemma triple_ifthenelse: forall P Q b c1 c2,
      ⦃⦃ atrue b //\\ P ⦄⦄ c1 ⦃⦃ Q ⦄⦄ ->
      ⦃⦃ afalse b //\\ P ⦄⦄ c2 ⦃⦃ Q ⦄⦄ ->
      ⦃⦃ P ⦄⦄ IFTHENELSE b c1 c2 ⦃⦃ Q ⦄⦄.
Proof.
move=>?? b c1 c2 H1 H2 s ?; pfold; apply: safe_step=>// c' s' R.
case: {-2}_ {-1}_ / R (erefl (IFTHENELSE b c1 c2, s)) (erefl (c', s'))=>// ????.
case=>->->->->; case=>->->.
by left; case/boolP: (beval _ _)=>B; [apply: H1|apply: H2].
Qed.

Lemma triple_havoc: forall x Q,
      ⦃⦃ aforall (fun n => aupdate x (CONST n) Q) ⦄⦄ HAVOC x ⦃⦃ Q ⦄⦄.
Proof.
move=>x ? s H; pfold; apply: safe_step=>// c' s' R.
case: {-2}_ {-1}_ / R (erefl (HAVOC x, s)) (erefl (c', s'))=>// ???.
case=>->->; case=>->->.
by left; pfold; apply/safe_now/H.
Qed.

Lemma triple_assert: forall b P,
      ⦃⦃ atrue b //\\ P ⦄⦄ ASSERT b ⦃⦃ atrue b //\\ P ⦄⦄.
Proof.
move=>b ? s [PR ?]; pfold; apply: safe_step=>//=; first by rewrite PR.
move=>c' s' R.
case: {-2}_ {-1}_ / R (erefl (ASSERT b, s)) (erefl (c', s'))=>// ?? B.
case=>EB ES; case=>->->; rewrite {}EB {}ES in B *.
by left; pfold; apply: safe_now.
Qed.

Lemma triple_consequence: forall P Q P' Q' c,
      ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄ -> P' -->> P -> Q -->> Q' ->
      ⦃⦃ P' ⦄⦄ c ⦃⦃ Q' ⦄⦄.
Proof.
move=>? Q ? Q' ? H H1 H2 ??.
have REC: forall c s, safe Q c s -> safe Q' c s.
- pcofix CH=>?? S; punfold S; pfold; case: S=>??.
  - by move=>??; apply/safe_now/H2.
  - move=>?? ST; apply: safe_step=>// ?? R.
    by right; apply: CH; case: (ST _ _ R).
by apply/REC/H/H1.
Qed.

Theorem Hoare_sound:
  forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄.
Proof.
move=>???; elim.
- by apply: triple_skip.
- by apply: triple_assign.
- by move=>?????? H ??; apply: triple_seq; first by exact: H.
- by move=>*; apply: triple_ifthenelse.
- by move=>*; apply: triple_while.
- by apply: triple_havoc.
- by move=>*; apply: triple_assert.
- by move=>?????? H ??; apply: triple_consequence; first by exact: H.
Qed.

End Soundness3.

(** *** Soundness of weak Hoare logic, using a step-indexed "safe" predicate. *)

Module Soundness4.

Inductive safe (Q: assertion): nat -> com -> store -> Prop :=
  | safe_zero: forall c s,
      safe Q O c s
  | safe_now: forall n c s,
      terminated c -> Q s ->
      safe Q (S n) c s
  | safe_step: forall n c s,
      ~terminated c -> ~error c s ->
      (forall c' s', red (c, s) (c', s') -> safe Q n c' s') ->
      safe Q (S n) c s.

Definition triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall n s, P s -> safe Q n c s.

Notation "⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄" := (triple P c Q) (at level 90, c at next level).

(** Properties of [safe]. *)

Lemma safe_mono:
  forall Q n c s, safe Q n c s -> forall n', (n' <= n)%nat -> safe Q n' c s.
Proof.
move=>????; elim.
- by move=>???; rewrite leqn0=>/eqP->; exact: safe_zero.
- move=>?????; case=>[?|??]; first by exact: safe_zero.
  by apply: safe_now.
- move=>?????? H2; case=>[?|??]; first by exact: safe_zero.
  by apply: safe_step=>// ???; apply: H2.
Qed.

Lemma safe_now': forall (Q: assertion) n c s,
  terminated c -> Q s -> safe Q n c s.
Proof.
move=>?; case.
- by move=>????; exact: safe_zero.
- by move=>?????; apply: safe_now.
Qed.

Lemma safe_terminated_inv: forall Q n c s,
  safe Q (S n) c s -> terminated c -> Q s.
Proof.
move=>? n c ? HS HT.
case: {-1}_ {-2}_ _ / HS (erefl (S n)) (erefl c)=>//.
move=>??? NT _ _ _ EC.
by rewrite EC in NT; rewrite HT /terminated in NT.
Qed.

Lemma safe_notstuck: forall Q n c s,
  safe Q (S n) c s -> ~error c s.
Proof.
move=>? n c ? H.
case: {-1}_ {-2}_ _ / H (erefl (S n)) (erefl c)=>//.
by rewrite /terminated=>???-> /= ???.
Qed.

Lemma safe_step_inv: forall Q n c s c' s',
  safe Q (S n) c s -> red (c, s) (c', s') -> safe Q n c' s'.
Proof.
move=>? n c s ?? H R.
case: {-1}_ {-2}_ {-2}_ / H (erefl (S n)) (erefl c) (erefl s)=>//.
- move=>??? T ?? EC.
  rewrite EC /terminated in T; rewrite T in R.
  by case: {-1}_ _ / R (erefl (SKIP, s)).
- move=>????? H; case=>-> EC ES; rewrite {}EC {}ES in H.
  by apply: H.
Qed.

(** Deduction rules. *)

Lemma triple_skip: forall P,
      ⦃⦃ P ⦄⦄ SKIP ⦃⦃ P ⦄⦄.
Proof.
by move=>????; apply: safe_now'.
Qed.

Lemma triple_assign: forall P x a,
      ⦃⦃ aupdate x a P ⦄⦄ ASSIGN x a ⦃⦃ P ⦄⦄.
Proof.
move=>? x a n s ?; case: n; first by exact: safe_zero.
move=>?; apply: safe_step=>// c' s' R.
case: {-2}_ {-1}_ / R (erefl (ASSIGN x a, s)) (erefl (c', s'))=>// ???.
case=>->->->; case=>->->.
by apply: triple_skip.
Qed.

Remark safe_seq:
  forall (Q R: assertion) (c': com) n,
  (forall n' s, (n' < n)%nat -> Q s -> safe R n' c' s) ->
  forall c s, safe Q n c s -> safe R n (c ;; c') s.
Proof.
move=>?? c0; elim.
- by move=>????; exact: safe_zero.
- move=>? IH QR c s H; apply: safe_step=>//=; first by apply/safe_notstuck/H.
  move=>c' s' R.
  case: {-2}_ {-1}_ / R (erefl (c;;c0, s)) (erefl (c', s'))=>//.
  - move=>??; case=>EC->->; case=>->->.
    apply: QR; first by exact: ltnSn.
    apply: safe_terminated_inv; first by exact: H.
    by rewrite -EC.
  - move=>????? R; case=>EC->ES; case=>->->; rewrite {}EC {}ES in R.
    apply: IH.
    - move=>????; apply: QR=>//.
      by rewrite ltnS; apply: ltnW.
    by apply: safe_step_inv; first by exact: H.
Qed.

Lemma triple_seq: forall P Q R c1 c2,
      ⦃⦃ P ⦄⦄ c1 ⦃⦃ Q ⦄⦄ -> ⦃⦃ Q ⦄⦄ c2 ⦃⦃ R ⦄⦄ ->
      ⦃⦃ P ⦄⦄ c1;;c2 ⦃⦃ R ⦄⦄.
Proof.
move=>? Q ??? H1 H2 ???.
by apply: (safe_seq Q); [move=>???; apply: H2|apply: H1].
Qed.

Lemma triple_while: forall P b c,
   ⦃⦃ atrue b //\\ P ⦄⦄ c ⦃⦃ P  ⦄⦄ ->
   ⦃⦃ P ⦄⦄ WHILE b c ⦃⦃ afalse b //\\ P ⦄⦄.
Proof.
move=>P b c T; elim.
- by move=>??; exact: safe_zero.
move=>? IH s ?; apply: safe_step=>// c' s' R.
case: {-2}_ {-1}_ / R (erefl (WHILE b c, s)) (erefl (c', s'))=>// ??? B.
- case=>EB _ ES; case=>->->; rewrite {}EB {}ES in B *.
  by apply: triple_skip.
case=>EB -> ES; case=>->->; rewrite {}EB {}ES in B *.
apply/safe_seq/T=>// ????.
apply: safe_mono; first by apply: IH.
by apply: ltnW.
Qed.

Lemma triple_ifthenelse: forall P Q b c1 c2,
      ⦃⦃ atrue b //\\ P ⦄⦄ c1 ⦃⦃ Q ⦄⦄ ->
      ⦃⦃ afalse b //\\ P ⦄⦄ c2 ⦃⦃ Q ⦄⦄ ->
      ⦃⦃ P ⦄⦄ IFTHENELSE b c1 c2 ⦃⦃ Q ⦄⦄.
Proof.
move=>?? b c1 c2 HT HF n s ?; case: n; first by exact: safe_zero.
move=>?; apply: safe_step=>// c' s' R.
case: {-2}_ {-1}_ / R (erefl (IFTHENELSE b c1 c2, s)) (erefl (c', s'))=>// ????.
case=>->->->->; case=>->->.
by case/boolP: (beval _ _)=>?; [apply: HT|apply: HF].
Qed.

Lemma triple_havoc: forall x Q,
      ⦃⦃ aforall (fun n => aupdate x (CONST n) Q) ⦄⦄ HAVOC x ⦃⦃ Q ⦄⦄.
Proof.
move=>x ? n s H; case: n; first by exact: safe_zero.
move=>?; apply: safe_step=>// c' s' R.
case: {-2}_ {-1}_ / R (erefl (HAVOC x, s)) (erefl (c', s'))=>// ???.
case=>->->; case=>->->.
by apply/safe_now'/H.
Qed.

Lemma triple_assert: forall b P,
      ⦃⦃ atrue b //\\ P ⦄⦄ ASSERT b ⦃⦃ atrue b //\\ P ⦄⦄.
Proof.
move=>b ? n s [A ?]; case: n; first by exact: safe_zero.
move=>?; apply: safe_step=>//=.
- by rewrite /atrue in A; rewrite A.
move=>c' s' R.
case: {-2}_ {-1}_ / R (erefl (ASSERT b, s)) (erefl (c', s'))=>// ?? B.
case=>EB ES; case=>->->; rewrite {}EB {}ES in B *.
by apply: safe_now'.
Qed.

Lemma triple_consequence: forall P Q P' Q' c,
      ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄ -> P' -->> P -> Q -->> Q' ->
      ⦃⦃ P' ⦄⦄ c ⦃⦃ Q' ⦄⦄.
Proof.
move=>? Q ? Q' ? H HP HQ ???.
have REC: forall n c s, safe Q n c s -> safe Q' n c s.
- move=>???; elim.
  - by exact: safe_zero.
  - by move=>?????; apply/safe_now/HQ.
  - by move=>???????; apply: safe_step.
by apply/REC/H/HP.
Qed.

Theorem Hoare_sound:
  forall P c Q, ⦃ P ⦄ c ⦃ Q ⦄ -> ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄.
Proof.
move=>???; elim.
- by apply: triple_skip.
- by apply: triple_assign.
- by move=>?????? H ??; apply: triple_seq; first by exact: H.
- by move=>*; apply: triple_ifthenelse.
- by move=>*; apply: triple_while.
- by apply: triple_havoc.
- by move=>*; apply: triple_assert.
- by move=>?????? H ??; apply: triple_consequence; first by exact: H.
Qed.

End Soundness4.

(** ** 2.5. Completeness *)

Module Completeness.

Import Soundness3.

(** A weakest (liberal) precondition, defined in terms
    of the operational semantics. *)

Definition sem_wp (c: com) (Q: assertion) : assertion :=
  fun s => safe Q c s.

Lemma terminated_dec: forall c, decidable (terminated c).
Proof.
by rewrite /terminated; case; try by [left|right].
Qed.

Lemma sem_wp_seq: forall c1 c2 Q s,
  sem_wp (c1 ;; c2) Q s -> sem_wp c1 (sem_wp c2 Q) s.
Proof.
rewrite /sem_wp=>+ c2 Q.
pcofix CH=>c1 s S; pfold.
case: (terminated_dec c1)=>T.
- apply: safe_now=>//.
  apply: safe_step_inv; first by exact: S.
  by rewrite T; exact: red_seq_done.
apply: safe_step=>//.
- suff: ~(error (c1;;c2) s) by [].
  by apply: safe_not_stuck=>//; exact: S.
move=>?? R; right; apply: CH.
apply: safe_step_inv; first by exact: S.
by apply: red_seq_step.
Qed.

(** Show that the triple [ { sem_wp c Q } c { Q } ] is derivable using the rules
    of Hoare logic. *)

Lemma Hoare_sem_wp:
  forall c Q, ⦃ sem_wp c Q ⦄ c ⦃ Q ⦄.
Proof.
elim.
- move=>?; apply: Hoare_consequence_pre; first by exact: Hoare_skip.
  by move=>? W; apply: safe_terminated_inv; first by exact: W.
- move=>x a Q; apply: Hoare_consequence_pre; first by exact: Hoare_assign.
  move=>s ?.
  apply: (@safe_terminated_inv _ _ (update x (aeval a s) s))=>//.
  by apply/safe_step_inv/red_assign.
- move=>? IH1 c2 ? Q; apply: (@Hoare_seq _ (sem_wp c2 Q))=>//.
  apply: Hoare_consequence_pre; first by apply: IH1.
  move=>?; by exact: sem_wp_seq.
- move=>b c1 IH1 c2 IH2 ?; apply: Hoare_ifthenelse.
  - apply: Hoare_consequence_pre; first by apply: IH1.
    move=>s [A B].
    have ->: (c1 = if beval b s then c1 else c2) by rewrite A.
    apply: safe_step_inv; first by apply: B.
    by apply: red_ifthenelse.
  - apply: Hoare_consequence_pre; first by apply: IH2.
    move=>s [A B].
    have ->: (c2 = if beval b s then c1 else c2) by move/negPf: A=>->.
    apply: safe_step_inv; first by apply: B.
    by apply: red_ifthenelse.
- move=>?? IH ?; apply: Hoare_consequence_post.
  - apply/Hoare_while/Hoare_consequence_pre; first by apply: IH.
    move=>?[? B]; apply/sem_wp_seq/safe_step_inv; first by apply: B.
    by apply: red_while_loop.
  move=>?[? B]; apply: (safe_terminated_inv _ SKIP)=>//.
  apply: safe_step_inv; first by apply: B.
  by apply: red_while_done.
- move=>b Q; apply: Hoare_consequence; first by [apply: (Hoare_assert Q)]; last by move=>? [].
  move=>s H.
  suff: beval b s.
  - split=>//; apply: (safe_terminated_inv _ SKIP)=>//.
    by apply: safe_step_inv; [apply: H | apply: red_assert].
  apply/negPn/negP.
  by move/safe_not_stuck: H; apply.
move=>x ?; apply: Hoare_consequence_pre; first by apply: Hoare_havoc.
move=>s H n.
apply: (safe_terminated_inv _ _ (update x n s))=>//.
by apply: safe_step_inv; [apply: H| apply: red_havoc].
Qed.

(** Relative completeness follows. *)

Theorem Hoare_complete:
  forall P c Q, ⦃⦃ P ⦄⦄ c ⦃⦃ Q ⦄⦄ -> ⦃ P ⦄ c ⦃ Q ⦄.
Proof.
move=>? c Q H.
apply: (Hoare_consequence_pre (sem_wp c Q)); first by apply: Hoare_sem_wp.
by move=>?; apply: H.
Qed.

End Completeness.

(** ** 2.6. Calculating weakest preconditions and verification conditions *)

Module WP.

(** Annotated commands. *)

Inductive com: Type :=
  | SKIP                                     (**r do nothing *)
  | ASSIGN (x: ident) (a: aexp)              (**r assignment: [v := a] *)
  | SEQ (c1: com) (c2: com)                  (**r sequence: [c1; c2] *)
  | IFTHENELSE (b: bexp) (c1: com) (c2: com) (**r conditional: [if b then c1 else c2] *)
  | WHILE (Inv: assertion) (b: bexp) (c1: com) (**r loop: [while b do c1 done] *)
  | ASSERT (b: bexp)                         (**r assertion (error if false) *)
  | HAVOC (x: ident).                        (**r nondeterministic assignment *)

Fixpoint erase (c: com) :=
  match c with
  | SKIP => Hoare.SKIP
  | ASSIGN x a => Hoare.ASSIGN x a
  | SEQ c1 c2 => Hoare.SEQ (erase c1) (erase c2)
  | IFTHENELSE b c1 c2 => Hoare.IFTHENELSE b (erase c1) (erase c2)
  | WHILE _ b c => Hoare.WHILE b (erase c)
  | ASSERT b => Hoare.ASSERT b
  | HAVOC x => Hoare.HAVOC x
  end.

Fixpoint wlp (c: com) (Q: assertion) : assertion :=
  match c with
  | SKIP => Q
  | ASSIGN x a => aupdate x a Q
  | SEQ c1 c2 => wlp c1 (wlp c2 Q)
  | IFTHENELSE b c1 c2 => (atrue b //\\ wlp c1 Q) \\// (afalse b //\\ wlp c2 Q)
  | WHILE Inv _ _ => Inv
  | ASSERT b => atrue b //\\ Q
  | HAVOC x => aforall (fun n => aupdate x (CONST n) Q)
  end.

Fixpoint vcond (c: com) (Q: assertion) : Prop :=
  match c with
  | SKIP | ASSIGN _ _ => True
  | SEQ c1 c2 => vcond c1 (wlp c2 Q) /\ vcond c2 Q
  | IFTHENELSE b c1 c2 => vcond c1 Q /\ vcond c2 Q
  | WHILE Inv b c =>
      vcond c Inv /\
      (atrue b //\\ Inv -->> wlp c Inv) /\
      (afalse b //\\ Inv -->> Q)
  | ASSERT _ => True
  | HAVOC _ => True
  end.

Definition vcgen (P: assertion) (c: com) (Q: assertion) : Prop :=
  vcond c Q /\ (P -->> wlp c Q).

Lemma wlp_sound: forall c Q,
  vcond c Q -> ⦃ wlp c Q ⦄ erase c ⦃ Q ⦄.
Proof.
elim=>/=.
- by move=>??; apply: Hoare_skip.
- by move=>????; apply: Hoare_assign.
- by move=>? IH1 ? IH2 ?[??]; apply: Hoare_seq; [apply: IH1| apply: IH2].
- move=>?? IH1 ? IH2 ?[??]; apply: Hoare_ifthenelse.
  - apply: Hoare_consequence_pre; first by apply: IH1.
    move=> ?[B]; case; case=>//.
    by rewrite /afalse B.
  - apply: Hoare_consequence_pre; first by apply: IH2.
    move=> ?[B]; case; case=>// A.
    by rewrite /afalse A in B.
- move=>??? IH ?[?][?]; apply/Hoare_consequence_post/Hoare_while.
  by apply: Hoare_consequence_pre; first by apply: IH.
- move=>???; apply: Hoare_consequence_post; first by exact: Hoare_assert.
  by move=>? [].
- by move=>???; apply: Hoare_havoc.
Qed.

Theorem vcgen_sound: forall P c Q,
  vcgen P c Q -> ⦃ P ⦄ erase c ⦃ Q ⦄.
Proof.
by move=>???[?]; apply/Hoare_consequence_pre/wlp_sound.
Qed.

End WP.

(** ** 2.7. Calculating strongest postconditions and verification conditions *)

Module SP.

Import WP.  (**r for annotated commands *)

Fixpoint sp (P: assertion) (c: com) : assertion :=
  match c with
  | SKIP => P
  | ASSIGN x a => aexists (fun x0 => aexists (fun v => aequal (VAR x) v //\\ aupdate x (CONST x0) (P //\\ aequal a v)))
  | SEQ c1 c2 => sp (sp P c1) c2
  | IFTHENELSE b c1 c2 => sp (atrue b //\\ P) c1 \\// sp (afalse b //\\ P) c2
  | WHILE Inv b _ => afalse b //\\ Inv
  | ASSERT b => atrue b //\\ P
  | HAVOC x => aexists (fun n => aupdate x (CONST n) P)
  end.

Fixpoint vcond (P: assertion) (c: com) : Prop :=
  match c with
  | SKIP | ASSIGN _ _ => True
  | SEQ c1 c2 => vcond P c1 /\ vcond (sp P c1) c2
  | IFTHENELSE b c1 c2 => vcond (atrue b //\\ P) c1 /\ vcond (afalse b //\\ P) c2
  | WHILE Inv b c =>
      vcond (atrue b //\\ Inv) c /\
      (P -->> Inv) /\
      (sp (atrue b //\\ Inv) c -->> Inv)
  | ASSERT b =>
      (P -->> atrue b)
  | HAVOC _ => True
  end.

Definition vcgen (P: assertion) (c: com) (Q: assertion) : Prop :=
  vcond P c /\ (sp P c -->> Q).

Lemma sp_sound: forall c P,
  vcond P c -> ⦃ P ⦄ erase c ⦃ sp P c ⦄.
Proof.
elim=>/=.
- by move=>??; apply: Hoare_skip.
- by move=>????; apply: Floyd_assign.
- by move=>? IH1 ? IH2 ?[??]; apply: Hoare_seq; [apply: IH1| apply: IH2].
- move=>?? IH1 ? IH2 ?[??]; apply: Hoare_ifthenelse.
  - apply: Hoare_consequence_post; first by apply: IH1.
    by move=>??; left.
  - apply: Hoare_consequence_post; first by apply: IH2.
    by move=>??; right.
- move=>??? IH ?[?][A]B; apply/Hoare_consequence_pre/A.
  by apply/Hoare_while/Hoare_consequence_post/B/IH.
- move=>?? H; apply: Hoare_consequence_pre; first by exact: Hoare_assert.
  by move=>??; split=>//; apply: H.
- move=>x ??; apply: Hoare_consequence_pre; first by exact: Hoare_havoc.
  move=>s H n; exists (s x)=>/=.
  set s' := update x n s.
  set s'' := update x (s x) s'.
  have E : s = s''.
  - apply: functional_extensionality=>?; rewrite /s'' /s' /update; case: ifP.
    - by move/eqP=>->.
    - by move=>->.
  by rewrite E /s'' /s' in H.
Qed.

Theorem vcgen_sound: forall P c Q,
  vcgen P c Q -> ⦃ P ⦄ erase c ⦃ Q ⦄.
Proof.
by move=>???[?]; apply/Hoare_consequence_post/sp_sound.
Qed.

End SP.
