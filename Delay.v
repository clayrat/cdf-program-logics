(** The [delay] type and Capretta's partiality monad *)

(** The type [delay A] represents computations that produce a result
    of type [A] if they terminate, but can also diverge. *)

From Coq Require Import ssreflect ssrfun ssrbool.
From Paco Require Import paco.

CoInductive delay (A: Type) :=
  | now : A -> delay A
  | later : delay A -> delay A.

Arguments now [A].
Arguments later [A].

Lemma u_delay:
  forall {A: Type} (x: delay A),
  x = match x with now v => now v | later y => later y end.
Proof. by move=>?; case. Qed.

(*Ltac unroll_delay X := rewrite (u_delay X); cbn.*)

(** The monad structure. *)

Definition ret := now.

CoFixpoint bind {A B: Type} (d: delay A) (f: A -> delay B) :=
  match d with
  | now v => later (f v)
  | later d' => later (bind d' f)
  end.

(** [safe Q d] means: if the computation [d] terminates,
    its value satisfies predicate [Q].  It's like a postcondition
    in a weak Hoare triple. *)

Inductive safe_gen {A: Type} (Q: A -> Prop) (safe : delay A -> Prop) : delay A -> Prop :=
  | safe_now: forall a, Q a -> safe_gen Q safe (now a)
  | safe_later: forall d, safe d -> safe_gen Q safe (later d).

Lemma safe_gen_mono {A: Type} Q : monotone1 (safe_gen (A:=A) Q).
Proof.
rewrite /monotone1=>??? IN LE.
elim: IN.
- by move=>??; apply: safe_now.
- by move=>??; apply/safe_later/LE.
Qed.

#[export] Hint Resolve safe_gen_mono : paco.

Definition safe {A : Type} Q d := paco1 (safe_gen (A:=A) Q) bot1 d.

Lemma safe_inv_now: forall {A: Type} (Q: A -> Prop) v,
  safe Q (now v) -> Q v.
Proof.
move=>?? v H; punfold H.
by case: {-1}_ / H (erefl (now v))=>// ??[->].
Qed.

Lemma safe_inv_later: forall {A: Type} (Q: A -> Prop) d,
  safe Q (later d) -> safe Q d.
Proof.
move=>?? d H; punfold H; pfold.
case: {-1}_ / H (erefl (later d))=>// ? s[->]; pclearbot.
by punfold s.
Qed.

Lemma safe_consequence:
  forall {A: Type} (Q1 Q2: A -> Prop),
  (forall a, Q1 a -> Q2 a) ->
  forall (d: delay A), safe Q1 d -> safe Q2 d.
Proof.
move=>? Q1 ? HI; pcofix CIH=>d S; punfold S; pfold.
case: {-1}_ / S (erefl d)=>//.
- by move=>???; apply/safe_now/HI.
- move=>? H ?; pclearbot; punfold H.
  apply: safe_later; right.
  by apply: CIH; pfold.
Qed.

Lemma safe_bind:
  forall {A B: Type} (Q1: A -> Prop) (Q2: B -> Prop)
         (d: delay A) (f: A -> delay B),
  safe Q1 d -> (forall v, Q1 v -> safe Q2 (f v)) -> safe Q2 (bind d f).
Proof.
move=>????; pcofix CIH=>d f H0 H1.
rewrite (u_delay (bind d f)); case: d H0=>/=? H0; pfold.
- move: (safe_inv_now _ _ H0)=>?.
  apply: safe_later; left.
  by apply: paco1_mon; first by exact: H1.
- move: (safe_inv_later _ _ H0)=>?.
  apply: safe_later; right.
  by apply: CIH.
Qed.
