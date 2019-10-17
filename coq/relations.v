Set Implicit Arguments.

Section relations.

Variables A : Type.

Definition relation := 
  A -> A -> Prop.

Definition total (R : relation) : Prop := 
  forall x y : A, R x y \/ x = y \/ R y x.

Definition reflexive (R : relation) :=
  forall x, R x x.

Definition symmetric (R : relation) :=
  forall x y, R x y -> R y x.

Definition transitive (R : relation) :=
  forall x y z, R x y -> R y z -> R x z.

Definition equivalence (R : relation) :=
  reflexive R /\ symmetric R /\ transitive R.

Definition irreflexive (R : relation) :=
  forall x, ~ R x x.

Definition asymmetric (R : relation) :=
  forall x y, R x y -> ~ R y x.

Definition order (R : relation) :=
  irreflexive R /\ transitive R.

Definition composed (R S : relation) : relation := 
  fun a c => 
  exists b, R a b /\ S b c.

Definition invariant (R E : relation) :=
  forall x x' y y', 
  R x y -> E x x' -> E y y' -> R x' y'.

Definition order_up_to_eq (R E : relation) :=
   equivalence E /\ invariant R E /\ order R.

Definition total_up_to_eq (R E : relation) :=
  forall a b, R a b \/ E a b \/ R b a.

Definition subrel (R R' : relation) :=
  forall x y, R x y -> R' x y.

Definition samerel (R R' : relation) :=
  subrel R R' /\ subrel R' R.

Lemma subrel_refl : 
  forall R, subrel R R.
Proof.
  intros R x y H; exact H.
Qed.

Lemma subrel_trans : 
  forall R1 R2 R3, 
  subrel R1 R2 ->
  subrel R2 R3 ->
  subrel R1 R3.
Proof.
  intros R1 R2 R3 H12 H23 x y R1xy; apply H23; apply H12; exact R1xy.
Qed.

Definition Runion (R S : relation) : relation :=
  fun a b => 
  R a b \/ S a b.

Lemma Runion_symm (R S: relation) :
  subrel (Runion R S) (Runion S R).
Proof.
  intros a b ab.
  destruct ab as [Rab | Sab].
  right; trivial.
  left; trivial.
Qed.

Lemma Runion_elim (R S : relation) :
  subrel R S ->
  samerel (Runion R S) S.
Proof.
  intros sub.
  split.
  intros x y [Rxy | Sxy].
  apply sub; exact Rxy.
  exact Sxy.
  intros x y Sxy; right; exact Sxy.
Qed.  

(* (STANDARD) CLOSURES *)

Inductive refl_close (R : relation) : relation :=
  | refl_step : subrel R (refl_close R) 
  | refl_refl : reflexive (refl_close R).

Inductive trans_close (R : relation) : relation :=
  | trans_step  : subrel R (trans_close R)
  | trans_trans : transitive (trans_close R).

Inductive refl_trans_close (R : relation) : relation :=
  | refl_trans_step  : subrel R (refl_trans_close R)
  | refl_trans_refl  : reflexive (refl_trans_close R) 
  | refl_trans_trans : transitive (refl_trans_close R).

Lemma refl_trans_monotone_trans : 
  forall R S,  
  subrel R (refl_trans_close S) -> 
  subrel (refl_trans_close R) (refl_trans_close S).
Proof.
  intros R S RS.
  red.
  induction 1 as [x y Rxy | x | x y z _ Sxy _ Syz].
  apply RS; apply Rxy.
  apply refl_trans_refl.
  exact (refl_trans_trans Sxy Syz).
Qed.

Lemma refl_trans_monotone : 
  forall R S,  
  subrel R S -> 
  subrel (refl_trans_close R) (refl_trans_close S).
Proof.
  intros R S RS.
  apply refl_trans_monotone_trans.
  apply (subrel_trans RS (refl_trans_step S)).
Qed.

Lemma trans_Runion_elim :
  forall R S,
  subrel R S ->
  samerel (refl_trans_close (Runion R S))
         (refl_trans_close S).
Proof.
  intros R S sub.
  split.
  apply refl_trans_monotone.
  apply Runion_elim.
  exact sub.
  apply refl_trans_monotone.
  apply Runion_elim.
  exact sub.
Qed.

(* ALTERNATIVE REFLEXIVE TRANSITIVE CLOSURE *)

Inductive refl_trans_close' (R : relation) : relation :=
  | refl_trans_close'_refl : reflexive (refl_trans_close' R)
  | refl_trans_close'_ltrans : forall x y z, R x y -> refl_trans_close' R y z -> refl_trans_close' R x z.

Lemma refl_trans_close'_step (R : relation) :
  forall x y,
  R x y ->
  refl_trans_close' R x y.
Proof.
  intros x y Rxy.
  apply refl_trans_close'_ltrans with (1:=Rxy).
  apply refl_trans_close'_refl.
Qed.

Lemma refl_trans_close'_trans (R : relation) :
  transitive (refl_trans_close' R).
Proof.
  red.
  induction 1 as [x | x y u Rxy Tyu IH]; [ intros Txz | intros Tuz].
  exact Txz.
  apply refl_trans_close'_ltrans with (1:=Rxy).
  exact (IH Tuz).
Qed.

Lemma samerel_refl_trans_close_refl_trans_close' (R : relation) : 
  samerel (refl_trans_close R) (refl_trans_close' R).
Proof.
  split.
  red; induction 1 as [x y Rxy | x | x y z Txy IHxy Tyz IHyz].
  apply refl_trans_close'_step with (1:=Rxy).
  apply refl_trans_close'_refl.
  apply refl_trans_close'_trans with (1:=IHxy)(2:=IHyz).
  red; induction 1 as [x | x y z Rxy Tyz IH].
  apply refl_trans_refl.
  apply refl_trans_trans with (2:=IH).
  apply refl_trans_step with (1:=Rxy).
Qed.

(* N-FOLD COMPOSITION *)

Fixpoint nfold (R : relation) (n : nat) : relation :=
  match n with 
      0 => fun x y => x = y
    | S m => composed R (nfold R m)
  end.

Lemma refl_trans_nfold (R : relation) : 
  samerel (refl_trans_close R) (fun a b => exists n, nfold R n a b).
Proof.
  split; intros a b H.
  assert (H' := proj1 (samerel_refl_trans_close_refl_trans_close' R) a b H).
  clear H; rename H' into H.
  induction H as [ a | a b c ab _ IH].
  exists 0; simpl; trivial.
  destruct IH as [n bc].
  exists (S n); simpl.
  exists b; split; assumption.
  destruct H as [n H].
  generalize a b H; clear H a b.
  induction n as [| n IH]; simpl; intros a b H.
  rewrite <- H; apply refl_trans_refl.
  destruct H as [a' [aa' a'b]].
  apply refl_trans_trans with a'.
  apply refl_trans_step with (1:=aa').
  apply IH with (1:=a'b).
Qed.

(* CONFLUENCE *)

Definition diamond (R : relation) : Prop := 
  forall a b c, 
  R a b ->  
  R a c -> 
  exists d, 
  R b d /\ R c d.

Definition confluent (R : relation) : Prop := 
  diamond (refl_trans_close R).

Lemma confluent_eq :
  forall R S,
  samerel R S ->
  confluent R -> confluent S.  
Proof.
  intros R S [RsubS SsubR] Rcr a b c ab ac.
  apply (refl_trans_monotone SsubR) in ab.
  apply (refl_trans_monotone SsubR) in ac.
  destruct (Rcr a b c ab ac) as [d [bd cd]].
  apply (refl_trans_monotone RsubS) in bd.
  apply (refl_trans_monotone RsubS) in cd.
  exists d; split; trivial.
Qed.

(* STRIP LEMMA *)

Definition strip (R : relation) : Prop := 
  forall a b c, 
  R a b ->  
  refl_trans_close R a c -> 
  exists d, 
  refl_trans_close R b d /\ refl_trans_close R c d.

Lemma strip_lemma : 
   forall (R : relation), strip R -> confluent R.
Proof.
  intros R Rstrip a b c Rab.
  apply samerel_refl_trans_close_refl_trans_close' in Rab.
  generalize c; clear c.
  induction Rab; intros c Rxc.
  exists c; split.
  exact Rxc.
  apply refl_trans_refl.
  destruct (Rstrip x y c H Rxc) as [d' [Ryd' Rcd']].
  destruct (IHRab d' Ryd') as [d [Rzd Rd'd]].
  exists d; split.
  exact Rzd.
  apply refl_trans_trans with d'.
  exact Rcd'.
  exact Rd'd.
Qed.

End relations.

Notation "R ; S" := (composed R S) (at level 38, right associativity).
Notation "R (+) S" := (Runion R S) (at level 38, right associativity).
Notation "R #" := (refl_close R) (at level 34, left associativity).
Notation "R +" := (trans_close R) (at level 34, left associativity).
Notation "R *" := (refl_trans_close R) (at level 34, left associativity).

Section indexed_relations.

Variables (I A : Set).

Definition Rfam := 
  I -> relation A.

Definition Rfam_union (R_ : Rfam) : relation A := 
  fun a b => 
  exists i : I, R_ i a b.

Definition Rfam_union_P (R_ : Rfam) (P : I -> Prop) : relation A := 
  fun a b => 
  exists i : I, P i /\ R_ i a b.

Definition Rfam_union_S (R_ : Rfam) (S : relation I) (j : I) : relation A := 
  Rfam_union_P R_ (fun i => S i j).

Lemma subrel_Rfam_union_P (P P' : I -> Prop) (R_ : Rfam) :
  (forall i, P i -> P' i) -> 
  subrel (Rfam_union_P R_ P) (Rfam_union_P R_ P').
Proof.
  intros PP' x y [i [Pi R_ixy]].
  exists i; split.
  apply PP'; exact Pi.
  exact R_ixy.
Qed. 

End indexed_relations.
