(* I will denote D- as a defined type. 
   For example, DTrue is defined True. *)

(* -- True -- *)

(* True is a single object, 1. *)

Inductive DTrue : Type :=
| DTrue_I : DTrue.

Theorem absurdity :
  True.
Proof.
  apply I. (* I is a unique object of True. *)
  Qed.

Theorem Dabsurdity :
  DTrue.
Proof.
  apply DTrue_I. Qed.

Theorem true_useless : forall A : Prop,
  True -> A.
Proof.
  intro A. intro HTrue. Abort.
  (* We can't create anything from True. *)

(* -- False -- *)

Inductive DFalse : Type := . 
(* False is type with no element. *)

Theorem false_not_provable : 
  False.
Proof.
  Abort.
  (* We can't prove something is false. *)

Theorem false_always_true : forall A : Prop,
  False -> A.
Proof.
  intro A. intro HFalse. inversion HFalse. Qed.

Theorem Dfalse_always_true : forall A : Prop,
  DFalse -> A.
Proof.
  intro A. intro HFalse. inversion HFalse. Qed.

Theorem false_always_true2 : forall A : Prop,
  1 = 2 -> A.
Proof.
  intro A. intro Hneq. discriminate. Qed.

Theorem false_is_false :
  ~ False.
Proof.
  intro f. apply f. Qed.

(* -- Imply -- *)

(* Imply is a function. 
   Actually, it is *computable* function. *)
Definition DImply (A : Type) (B : Type) := A -> B.

Theorem Imply_prove :
  forall (n m : nat), n = m -> S n = S m.
Proof.
  intros n m Heq. rewrite Heq. reflexivity. Qed.

Theorem Imply_left : forall (A B : Prop),
  A -> (A -> B) -> B.
Proof.
  intros A B HA HAB.
  apply HAB in HA. apply HA. Qed.

Theorem Imply_right : forall (A B : Prop),
  A -> (A -> B) -> B.
Proof.
  intros A B HA HAB.
  apply HAB. apply HA. Qed.

(* -- And -- *)

(* And is simply a pair of two type. *)
Inductive DAnd (A : Type) (B : Type) :=
| DPair (a : A) (b : B).

Theorem And_left : forall A B : Prop,
  A /\ B -> A.
Proof.
  intros A B HAB. destruct HAB as [HA HB]. apply HA. Qed.

Theorem And_right : forall A B : Prop,
  A /\ B -> B.
Proof.
  intros A B HAB. destruct HAB as [HA HB]. apply HB. Qed.

Theorem And_construct : forall A B : Prop,
  A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
  Qed.

Theorem And_commute : forall A B : Prop,
  A /\ B -> B /\ A.
Proof.
  intros A B HAB. destruct HAB as [HA HB]. split.
  - apply HB.
  - apply HA.
  Qed.

Axiom le_trans : forall n m l,
  n <= m -> m <= l -> n <= l.

Axiom le_false : forall n,
  S n <= n -> False.

Theorem And_ex : forall n m,
  n <= m /\ m <= n -> n = m.
Proof.
  intros. destruct H as [H1 H2].
  inversion H1.
  - reflexivity.
  - subst. apply le_trans with (S m0) n m0 in H2.
    + apply le_false in H2. inversion H2.
    + apply H.
  Qed.

(* -- Or -- *)

(* Or is either a left type or right type. 
   You can think it as disjoint union.
   More category theoritic explanation is sum. *)
Inductive DOr (A : Type) (B : Type) :=
| DLeft (a : A)
| DRight (b : B).

Theorem Or_left : forall A B : Prop,
  A -> A \/ B.
Proof.
  intros A B HA. left. apply HA. Qed.

Theorem Or_right : forall A B : Prop,
  B -> A \/ B.
Proof.
  intros A B HB. right. apply HB. Qed.

Theorem Or_Prove : forall A B C : Prop,
  (A -> C) -> (B -> C) -> (A \/ B) -> C.
Proof.
  intros A B C HAC HBC HAB.
  destruct HAB as [HA | HB].
  - apply HAC. apply HA.
  - apply HBC. apply HB.
  Qed.

Theorem Or_commute : forall A B : Prop,
  A \/ B -> B \/ A.
Proof.
  intros A B HAB.
  destruct HAB as [HA | HB].
  - right. apply HA.
  - left. apply HB.
  Qed.

Theorem Or_ex : forall n m,
  n < m \/ n = m \/ n > m.
Proof.
  intros. induction n.
  - destruct m.
    + right. left. reflexivity.
    + left. unfold lt. apply le_n_S. apply le_0_n.
  - destruct IHn as [H1 | [H2 | H3]].
    + unfold lt in H1. inversion H1.
      * right. left. reflexivity.
      * subst. left. unfold lt. apply le_n_S. apply H.
    + subst. right. right. unfold gt. unfold lt. apply le_n.
    + right. right. unfold gt in *. unfold lt in *.
      apply le_S. apply H3.
  Qed.

(* Forall *)

(* Forall is a dependent function. 
   But to implement forall, you need to use forall. *)

(* And you've seen all the examples before! *)

(* Exists *)

(* Exists is a dependent pair. *)
Inductive DExists (A : Type) (t : A -> Type) :=
| DepPair (a : A) (b : t a).

Theorem nat_0_or_minus :
  forall (n : nat), n = 0 \/ exists n', n = S n'.
Proof.
  intro. destruct n.
  - left. reflexivity.
  - right. exists n. reflexivity.
  Qed.

(* Induction *)
Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).

Inductive le' : nat -> nat -> Prop :=
| le_n' (n : nat) : le' n n
| le_S' (n m : nat) (H : le' n m) : le' n (S m).

Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem even_spec :
  forall n, even n -> exists k, n = 2 * k.
Proof.
  intros n Heven. induction Heven.
  - exists 0. simpl. reflexivity.
  - destruct IHHeven as [k Hk]. rewrite Hk. exists (S k).
    simpl. apply eq_S. rewrite <- plus_n_O. apply plus_n_Sm.
  Qed.

Theorem le_spec :
  forall n m, n <= m -> exists k, m = n + k.
Proof.
  intros. induction H.
  - exists 0. apply plus_n_O.
  - destruct IHle as [k Hk].
    exists (S k). rewrite Hk. apply plus_n_Sm.
  Qed.

Check nat_ind.

(* Recursive Functions *)

Fixpoint add (n m : nat) : nat :=
  match n with
  | 0 => m
  | S n' => S (add n' m)
  end.

(* add is recursively defined (decreasing on 1st argument) *)

Fail Fixpoint false_proof (n : nat) : False :=
  false_proof n.

(* Coinduction *)
CoInductive Seq : Type :=
| CCons (n : nat) (S : Seq) : Seq.

CoFixpoint increase (n : nat) : Seq :=
  CCons n (increase (S n)).

Fail CoFixpoint wrong (n : nat) : Seq :=
  wrong (S n).

(* Equality *)

(* Equality is Refl for all element of type. *)
Inductive DEqual (A : Type) :=
| DRefl (a : A). 

Theorem eq_refl' : forall (A : Type) (a : A),
  a = a.
Proof.
  intros A a. reflexivity. Qed.

Theorem eq_sym' : forall (A : Type) (a b : A) (H : a = b),
  b = a.
Proof.
  intros A a b Heq. rewrite Heq. reflexivity. Qed.

Theorem eq_trans' : forall (A : Type) (a b c : A) 
  (H1 : a = b) (H2 : b = c),
  a = c.
Proof.
  intros A a b c Heq1 Heq2. rewrite Heq1. apply Heq2. Qed.

Theorem homotopy_lifting_property : 
  forall (A : Type) (a b : A) (P : A -> Prop),
  a = b -> P a -> P b.
Proof.
  intros A a b P Heq HPa. rewrite Heq in HPa. apply HPa. Qed.

(* What is unprovable? *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

Theorem em_irrefutable : forall P : Prop,
  ~~ (P \/ ~ P).
Proof.
  intros P H. apply H.
  right. intros p. apply H. left. apply p. Qed.

Require Export Coq.omega.Omega.

Theorem And_auto : forall n m,
  n <= m /\ m <= n -> n = m.
Proof.
  intros. omega. Qed.

Theorem Or_auto : forall n m,
  n < m \/ n = m \/ n > m.
Proof.
  intros. omega. Qed.




