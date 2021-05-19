(** A library of operators over relations,
    to define transition sequences and their properties. *)

From Coq Require Import ssreflect.

Set Implicit Arguments.

Section SEQUENCES.

Variable A: Type.                 (**r the type of states *)
Variable R: A -> A -> Prop.       (**r the transition relation between states *)

(** ** Finite sequences of transitions *)

(** Zero, one or several transitions: reflexive transitive closure of [R]. *)

Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Lemma star_one:
  forall (a b: A), R a b -> star a b.
Proof.
move=>???.
by apply/star_step/star_refl.
Qed.

Lemma star_trans:
  forall (a b: A), star a b -> forall c, star b c -> star a c.
Proof.
move=>a b; elim=>// ????? IH ??.
by apply/star_step/IH.
Qed.

(** One or several transitions: transitive closure of [R]. *)

Inductive plus: A -> A -> Prop :=
  | plus_left: forall a b c,
      R a b -> star b c -> plus a c.

Lemma plus_one:
  forall a b, R a b -> plus a b.
Proof.
move=>???.
by apply/plus_left/star_refl.
Qed.

Lemma plus_star:
  forall a b,
  plus a b -> star a b.
Proof.
move=>??; case.
by exact: star_step.
Qed.

Lemma plus_star_trans:
  forall a b c, plus a b -> star b c -> plus a c.
Proof.
move=>???; case=>???? H1 H2.
by apply/plus_left/star_trans/H2/H1.
Qed.

Lemma star_plus_trans:
  forall a b c, star a b -> plus b c -> plus a c.
Proof.
move=>???; case=>// ? b c HR HS.
case: {-1}_ {-2}_ / HS (eq_refl b) (eq_refl c).
- move=>? EQ1 _ H; rewrite {}EQ1 in HR.
  by apply/plus_left/plus_star/H.
- move=>???? HS1 EQ1 _ H; rewrite EQ1 in HR.
  by apply/(plus_left HR)/star_trans/plus_star/H/star_step/HS1.
Qed.

Lemma plus_right:
  forall a b c, star a b -> R b c -> plus a c.
Proof.
move=>???? H2.
by apply/star_plus_trans/plus_one/H2.
Qed.

(** Absence of transitions from a state. *)

Definition irred (a: A) : Prop := forall b, ~(R a b).

(** A variant of [star] that counts the number of transitions. *)

Inductive starN: nat -> A -> A -> Prop :=
  | starN_refl: forall a,
      starN O a a
  | starN_step: forall n a b c,
      R a b -> starN n b c -> starN (S n) a c.

Lemma starN_star:
  forall n a b, starN n a b -> star a b.
Proof.
move=>n ??; elim.
- by move=>?; exact: star_refl.
- by move=>?????? H2; apply/star_step/H2.
Qed.

Lemma star_starN:
  forall a b, star a b -> exists n, starN n a b.
Proof.
move=>??; elim.
- by move=>?; exists 0; exact: starN_refl.
- move=>????? [n HS].
  by exists (S n); apply/starN_step/HS.
Qed.

(** ** Infinite transition sequences *)

(** It is easy to characterize the fact that all transition sequences starting
  from a state [a] are infinite: it suffices to say that any finite sequence
  starting from [a] can always be extended by one more transition. *)

Definition all_seq_inf (a: A) : Prop :=
  forall b, star a b -> exists c, R b c.

(** However, this is not the notion we are trying to characterize: the case
  where there exists an infinite sequence of transitions starting from [a],
  [a --> a1 --> a2 --> ... -> aN -> ...]
  leaving open the possibility that there exists finite sequences
  starting from [a].

  Example: consider [A = nat] and [R] such that [R 0 0] and [R 0 1].
  [all_seq_inf 0] does not hold, because a sequence [0 -->* 1] cannot
  be extended.  Yet, [R] admits an infinite sequence, namely
  [0 --> 0 --> ...].

  Another attempt would be to represent the sequence of states
  [a0 --> a1 --> a2 --> ... -> aN -> ...] explicitly, as a function
  [f: nat -> A] such that [f i] is the [i]-th state [ai] of the sequence. *)

Definition infseq_with_function (a: A) : Prop :=
  exists f: nat -> A, f 0 = a /\ forall i, R (f i) (f (S i)).

(** This is a correct characterization of the existence of an infinite
  sequence of reductions.  However, it is inconvenient to work with
  this definition in Coq's constructive logic: in most use cases, the
  function [f] is not computable and therefore cannot be defined in Coq.

  However, we do not really need the function [f]: its codomain [X] is
  all we need!  What matters is the existence of a set [X] such as
  [a] is in [X], and
  every [b] in [X] can make a transition to an element of [X].
  This suffices to prove the existence of an infinite sequence of transitions
  starting from [a].
*)

Definition infseq (a: A) : Prop :=
  exists X: A -> Prop,
  X a /\ (forall a1, X a1 -> exists a2, R a1 a2 /\ X a2).

(** This definition is essentially a coinduction principle.
  Let us show some expected properties.  For instance: if relation [R]
  contains a cycle, an infinite sequence exists. *)

Remark cycle_infseq:
  forall a, R a a -> infseq a.
Proof.
move=>a H.
exists (fun b => b = a); split=>// ? ->.
by exists a.
Qed.

(** More generally: if all sequences from [a] are infinite, there exists one
  infinite sequence starting in [a]. *)

Lemma infseq_if_all_seq_inf:
  forall a, all_seq_inf a -> infseq a.
Proof.
move=>??.
exists all_seq_inf; split=>// a1 HA1.
move: (HA1 a1 (star_refl _))=>[a2 R12].
exists a2; split=>// a3 S23.
move: (HA1 a3 (star_step R12 S23))=>[a4 R23].
by exists a4.
Qed.

(** Likewise, the characterization [infseq_with_function] based on functions
  implies [infseq]. *)

Lemma infseq_from_function:
  forall a, infseq_with_function a -> infseq a.
Proof.
move=>? [f [??]].
exists (fun a => exists i, f i = a); split.
- by exists 0.
- move=>a1 [i <-].
  exists (f (S i)); split=>//.
  by exists (S i).
Qed.

(** An "inversion lemma" for [infseq]: if [infseq a], i.e. there exists
  an infinite sequence starting in [a], then [a] can transition to a state [b]
  that satisfies [infseq b]. *)

Lemma infseq_inv:
  forall a, infseq a -> exists b, R a b /\ infseq b.
Proof.
move=>a [X [Xa XP]].
move: (XP a Xa)=>[b [??]].
exists b; split=>//.
by exists X.
Qed.

(** A very useful coinduction principle considers a set [X] where for
  every [a] in [X], we can make one *or several* transitions to reach
  a state [b] that belongs to [X].  *)

Lemma infseq_coinduction_principle:
  forall (X: A -> Prop),
  (forall a, X a -> exists b, plus a b /\ X b) ->
  forall a, X a -> infseq a.
Proof.

move=>X H a0 Xa0.
exists (fun a => exists b, star a b /\ X b); split.
- exists a0; split=>//; exact: star_refl.
- move=>a1 [a2 [S12 X2]].
  case: {-2}_ {-2}_ / S12 (eq_refl a1) (eq_refl a2).
  + move=>? _ ->.
    move: (H a2 X2)=>[a3 [P23 X3]].
    case: {-2}_ {-2}_ / P23 (eq_refl a2) (eq_refl a3) =>? b ?? S _ E.
    rewrite {}E in S.
    exists b; split=>//.
    by exists a3.
  + move=>? b ?? S _ E; rewrite {}E in S.
    exists b; split=>//.
    by exists a2.
Qed.

(** ** Determinism properties for functional transition relations. *)

(** A transition relation is functional if every state can transition
  to at most one other state. *)

Hypothesis R_functional:
  forall a b c, R a b -> R a c -> b = c.

(** Uniqueness of finite transition sequences. *)

Lemma star_star_inv:
  forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
Proof.
move=>??; elim.
- by move=>???; left.
- move=>a ?? HR S IH c S1.
  case: {-1}_ {-2}_ / S1 (eq_refl a) (eq_refl c).
  + move=>? E1 E2. rewrite {}E1 {}E2 in HR *.
    by right; apply/star_step/S.
  + move=>??? HR2 S2 E1 E2; rewrite {}E1 in HR; rewrite {}E2 in S S2 *.
    by apply: IH; rewrite (R_functional HR HR2).
Qed.

Lemma finseq_unique:
  forall a b b',
  star a b -> irred b ->
  star a b' -> irred b' ->
  b = b'.
Proof.
move=>? b c S1 Ib S2 Ic.
case: (star_star_inv S1 S2)=>S.
- case: {-1}_ {-2}_ / S (eq_refl b) (eq_refl c) => // ??? HR _ E _; rewrite {}E in Ib.
  by exfalso; apply/Ib/HR.
- case: {-1}_ {-2}_ / S (eq_refl c) (eq_refl b) => // ??? HR _ E _; rewrite {}E in Ic.
  by exfalso; apply/Ic/HR.
Qed.

(** A state cannot both diverge and terminate on an irreducible state. *)

Lemma infseq_inv':
  forall a b, R a b -> infseq a -> infseq b.
Proof.
move=>?? Rab Ia.
move: (infseq_inv Ia)=>[? [Rab0 ?]].
by rewrite (R_functional Rab Rab0).
Qed.

Lemma infseq_star_inv:
  forall a b, star a b -> infseq a -> infseq b.
Proof.
move=>??; elim=>// ????? IH Ia1.
by apply/IH/infseq_inv'/Ia1.
Qed.

Lemma infseq_finseq_excl:
  forall a b,
  star a b -> irred b -> ~ infseq a.
Proof.
move=>? b S Ib I.
move: (infseq_star_inv S I) => /infseq_inv [c [? _]].
by apply: (Ib c).
Qed.

(** If there exists an infinite sequence of transitions from [a],
  all sequences of transitions arising from [a] are infinite. *)

Lemma infseq_all_seq_inf:
  forall a, infseq a -> all_seq_inf a.
Proof.
move=>? I ? S.
move: (infseq_star_inv S I) => /infseq_inv [c [? _]].
by exists c.
Qed.

End SEQUENCES.
