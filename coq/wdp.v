Require Import relations.

Set Implicit Arguments.

Section weak_diamond_property.

Variables (I A : Set) (R_ : Rfam I A) (L E : relation I).

Definition LE (x y : I) := L x y \/ E x y.

Notation "R_ << j" := (Rfam_union_S R_ L j) (at level 7, no associativity).
Notation "R_ <<= j" := (Rfam_union_S R_ (L (+) E) j) (at level 7, no associativity).

Definition curly (i : I) : relation A := R_<<i* ; R_ i # ; R_<<i*.
Notation "~~> j" := (curly j) (at level 7, no associativity).

Definition curlyn (i : I) (n : nat) : relation A := nfold (curly i) n.

(* The weak diamond property. *)

Definition weak_diamond_property :=
  forall a b c alpha beta,
  LE beta alpha ->
  R_ beta a c ->
  R_ alpha a b ->
  exists d : A, (
    ((R_<< beta)* ; R_ alpha # ; (R_<< alpha)*)  c d  /\  
    (R_<<= alpha)* b d /\
    (L beta alpha -> (R_<< alpha)* b d)
  ). 
  
Hypothesis oeq : order_up_to_eq L E.
Hypothesis teq : total_up_to_eq L E.
Hypothesis wfL : well_founded L.
Hypothesis wdp : weak_diamond_property.

Hypothesis REcongr : forall (i j : I), E i j -> samerel (R_ i) (R_ j).

Variable top : I.
Hypothesis top_top : forall i : I, i = top \/ L i top.

Variable bot : I.
Hypothesis bot_bot : forall i : I, i = bot \/ L bot i.
Hypothesis bot_id : samerel (R_ bot) (@eq A).

(* Lemmas *)

(* reflexive WDP *)
  
Lemma wdp_refl :
  forall a b c alpha beta,
  LE beta alpha ->
  (R_ beta #) a c ->
  (R_ alpha #) a b ->
  exists d : A, (
    ((R_<< beta)* ; R_ alpha # ; (R_<< alpha)*) c d  /\  
    (R_<<= alpha)* b d /\
    (L beta alpha -> (R_<< alpha)* b d)
  ).
Proof.
  intros a b c alpha beta LEba Rac Rab.
  destruct Rab as [a b Rab | a].
  destruct Rac as [a c Rac | a].
  (* none empty *)
  apply wdp with a.
  exact LEba.
  exact Rac.
  exact Rab.
  (* Rac empty *)
  exists b; split.
  exists a; split.
  apply refl_trans_refl.
  exists b; split.
  left; exact Rab.
  apply refl_trans_refl.
  split.
  apply refl_trans_refl.
  intro Lba.
  apply refl_trans_refl.
  destruct Rac as [a c Rac | a].
  (* Rab empty *)
  exists c; split.
  exists c; split.
  apply refl_trans_refl.
  exists c; split.
  right.
  apply refl_trans_refl.
  split.
  apply refl_trans_step.
  exists beta.
  split.
  destruct LEba as [Lba | Eba].
  left; exact Lba.
  right; exact Eba.
  exact Rac.
  intro Lba.
  apply refl_trans_step.
  exists beta; split.
  exact Lba.
  exact Rac.
  (* both empty *)
  exists a.
  split.
  exists a; split.
  apply refl_trans_refl.
  exists a; split.
  right.
  apply refl_trans_refl.
  split.
  apply refl_trans_refl.
  intro Lba; apply refl_trans_refl.
Qed.

(* Eq_star *)

Lemma eq_star :
  forall (X : Set),
  subrel (@eq X *) (@eq X).
Proof.
  intros X a b Rab.
  induction Rab; trivial.
  rewrite IHRab1; exact IHRab2.
Qed.

(* Lemmas about L and E *)

Lemma le_le :
  forall (a b c : I), 
  LE a b -> 
  LE b c ->
  LE a c.
Proof.
  destruct oeq as [[Erefl [Esymm Etrans]] [LEinv [_ Ltrans]]].
  intros a b c [ab | ab] [bc | bc].
  left; apply (Ltrans a b c ab bc).
  left; apply (LEinv a a b c ab (Erefl a) bc).
  left; apply (LEinv b a c c bc (Esymm a b ab) (Erefl c)).
  right; apply (Etrans a b c ab bc).
Qed.

Lemma le_lt :
  forall (a b c : I), 
  LE a b -> 
  L b c ->
  L a c.
Proof.
  destruct oeq as [[Erefl [Esymm Etrans]] [LEinv [_ Ltrans]]].
  intros a b c [ab | ab] bc.
  apply (Ltrans a b c ab bc).
  apply (LEinv b a c c bc (Esymm a b ab) (Erefl c)).
Qed.

Lemma lt_le :
  forall (a b c : I), 
  L a b -> 
  LE b c ->
  L a c.
Proof.
  destruct oeq as [[Erefl [Esymm Etrans]] [LEinv [_ Ltrans]]].
  intros a b c ab [bc | bc].
  apply (Ltrans a b c ab bc).
  apply (LEinv a a b c ab (Erefl a) bc).
Qed.

(* Lemmas about R_<<= and R_<< *)

Lemma lt_subrel_le :
  forall (i : I),
  subrel (R_<< i) (R_<<= i).
Proof.
  intros i x y lt.
  destruct lt as [z [Lzy Rzxy]].
  exists z.
  split.
  left.
  exact Lzy.
  exact Rzxy.
Qed.

Lemma red_incl_le :
  forall alpha beta, 
  LE alpha beta ->
  subrel (R_<<= alpha) (R_<<= beta).
Proof.
  intros alpha beta LEab.
  apply subrel_Rfam_union_P.
  intros i LEialpha.
  apply (le_le LEialpha LEab).
Qed.

Lemma red_incl_lt : 
  forall alpha beta, 
  L alpha beta ->
  subrel (R_<<= alpha) (R_<< beta).
Proof.
  intros alpha beta LEab.
  apply subrel_Rfam_union_P.
  intros i LEialpha.
  apply (le_lt LEialpha LEab).
Qed.

Lemma max_label : 
  forall (i j beta : I) (a b c d : A),
  L i beta ->
  (R_ <<= i *) a b ->
  L j beta ->
  (R_ <<= j *) c d 
  ->
  exists (gamma : I), L gamma beta /\
        (R_ <<= gamma *) a b /\ (R_ <<= gamma *) c d.
Proof.
  intros i j beta a b c d Lib Rab Ljb Rcd.
  destruct (teq i j) as [Lij | [Eij | Lji]].
  (* L i j *)
  exists j; split; [exact Ljb | split; [ | exact Rcd]].
  apply refl_trans_monotone with (R_<<= i).
  apply red_incl_le; left; exact Lij.
  exact Rab.
  (* E i j *)
  exists j; split; [exact Ljb | split].
  apply refl_trans_monotone with (R_<<= i).
  apply red_incl_le; right; exact Eij.
  exact Rab.
  exact Rcd.
  (* L j i *)
  exists i; split; [exact Lib | split; [exact Rab | ]].
  apply refl_trans_monotone with (R_<<= j).
  apply red_incl_le; left; exact Lji.
  exact Rcd.
Qed.

Lemma Rlt_eq :
  forall i j, 
  E i j ->
  subrel (R_<< i) (R_<< j).
Proof.
  intros i j Eij x y [i' [Li'i Rxy]].
  exists i'; split.
  apply lt_le with i.
  exact Li'i.
  right; exact Eij.
  exact Rxy.
Qed.

Lemma Rle_eq :
  forall i j, 
  E i j ->
  subrel (R_<<= i) (R_<<= j).
Proof.
  intros i j Eij x y [i' [Li'i Rxy]].
  exists i'; split.
  apply le_le with i.
  exact Li'i.
  right; exact Eij.
  exact Rxy.
Qed.

(* Lemmas about bot *)

Lemma bot_eq : 
  forall gamma, 
  E gamma bot -> 
  gamma = bot.
Proof.
  destruct oeq as [[Erefl _] [LinvE [Lirrefl _]]].
  intros gamma Egammabot.
  destruct (bot_bot gamma).
  exact H.
  assert (Lbotbot := LinvE bot bot gamma bot H (Erefl bot) Egammabot).
  destruct (Lirrefl bot Lbotbot). 
Qed.

Lemma bot_lt : 
  forall gamma, 
  ~(L gamma bot).
Proof.
  destruct oeq as [_ [_ [Lirrefl Ltrans]]].
  intros gamma Lgammabot.
  destruct (bot_bot gamma).
  rewrite H in Lgammabot.
  destruct (Lirrefl bot Lgammabot).
  destruct (Lirrefl bot (Ltrans bot gamma bot H Lgammabot)).  
Qed.

Lemma bot_red_step :
  forall gamma,
  E gamma bot ->
  subrel (R_ gamma) (@eq A).
Proof.
  intros gamma Egammabot.
  rewrite (bot_eq Egammabot).
  apply bot_id.
Qed.

Lemma bot_red_le :
  forall gamma,
  E gamma bot ->
  subrel ((R_<<= gamma)*) (@eq A).
Proof.
  intros gamma Egammabot.
  rewrite (bot_eq Egammabot).
  apply subrel_trans with (eq *).
  apply refl_trans_monotone.
  intros a b [i [LEibot Riab]].
  destruct LEibot.
  destruct (bot_lt H).
  rewrite (bot_eq H) in Riab.
  apply bot_id.
  exact Riab.
  apply eq_star.
Qed.

Lemma bot_red_lt :
  forall gamma,
  E gamma bot ->
  subrel ((R_<< gamma)*) (@eq A).
Proof.
  intros gamma Egb.
  apply subrel_trans with ((R_<<= gamma)*).
  apply refl_trans_monotone.
  apply lt_subrel_le.
  apply bot_red_le.
  exact Egb.
Qed.

Lemma lt_red_lt :
  forall beta, 
  forall a b, 
  (R_<< beta) * a b -> 
  (beta = bot /\ a = b)
  \/ (L bot beta /\ exists gamma, L gamma beta /\ (R_<<= gamma) * a b).
Proof.
  destruct oeq as [[Erefl [Esymm Etrans]] [LinvE [Lirrefl Ltrans]]].
  intros beta a b ab.
  pose proof (bot_bot beta) as [Ebetabot | Lbotbeta].
  (* bot = beta *)
  rewrite Ebetabot in *.
  left; split; [reflexivity | ].
  apply (bot_red_lt (Erefl bot)).
  exact ab.
  (* L bot beta *)
  right; split.
  exact Lbotbeta.
  (* induction *)
  induction ab as [a b ab | a | a b c ab IHab bc IHbc].
  (* step *)
  destruct ab as [i [Libeta Riab]].
  exists i; split; [exact Libeta | ].
  apply refl_trans_step; exists i; split. 
  right; apply Erefl.
  exact Riab.
  (* refl *)
  exists bot; split; [exact Lbotbeta | apply refl_trans_refl].
  (* trans *)
  destruct IHab as [u [Lubeta IHab]].
  destruct IHbc as [w [Lwbeta IHbc]].
  destruct (max_label Lubeta IHab Lwbeta IHbc) as [gamma [Lgammabeta [max_ab max_bc]]].
  exists gamma; split.
  exact Lgammabeta.
  apply refl_trans_trans with b; [exact max_ab | exact max_bc].
Qed.

(* Lemmas about ~~> *)

Lemma le_trans_eq_curly_trans :
  forall (i : I), samerel ((R_ <<= i)*) ((~~>i)*).
Proof.
  split.
  (* => direction *)
  apply refl_trans_monotone.
  intros x y [j [[Lji | Eij] Rjxy]].
  (* L j i *)
  exists y.
  split.
  apply refl_trans_step.
  exists j.
  split.
  exact Lji.
  exact Rjxy.
  exists y.
  split.
  right.
  apply refl_trans_refl.
  exists x.
  split.
  apply refl_trans_refl.
  (* E j i *)
  exists y.
  split.
  left.
  apply REcongr with (1:=Eij) (2:=Rjxy).
  apply refl_trans_refl.
  (* <= direction *)
  apply refl_trans_monotone_trans.
  intros x z xz.
  destruct xz as [y [xy [y' [yy' y'z]]]].
  apply refl_trans_trans with y.
  apply refl_trans_monotone with (R_<< i).
  apply lt_subrel_le.
  exact xy.
  apply refl_trans_trans with y'.
  destruct yy' as [y y' yy' | y].
  apply refl_trans_step.
  exists i.
  split.
  right.
  apply (proj1 (proj1 oeq)).
  exact yy'.
  apply refl_trans_refl.
  apply refl_trans_monotone with (R_ << i).
  apply lt_subrel_le.
  exact y'z.
Qed.

(* The main diagram X *)

Definition X (alpha beta : I) := 
  forall a b' b c,
  (R_<<= beta)* a c -> 
  (R_ alpha #) a b' ->
  (R_<< alpha)* b' b ->
  exists d, 
    (Runion (R_<< alpha) (R_<<= beta))* b d /\
    ((R_<< beta)* ; R_ alpha # ; (R_<< alpha)*) c d.

Lemma X_confluence : 
  forall i : I, 
  X i i ->
  confluent (R_<<= i).
Proof.
  destruct oeq as [[_ [Esymm _]] _].
  intros i Xii.
  apply strip_lemma.
  intros a b c ab ac.
  destruct ab as [j [LEji ab]].
  assert (H: exists d, ((R_<< i (+) R_<<= i) *) b d /\ (R_<< i *; R_ i #; R_<< i *) c d).
  destruct LEji as [Lji | Eji].
  apply (Xii a a b c); [exact ac | right | ].
  apply refl_trans_step. exists j; split; [exact Lji |  exact ab].
  apply (Xii a b b c); [exact ac | | ].
  left.
  apply REcongr with j.
  exact (Esymm j i Eji).
  exact ab.
  apply refl_trans_refl.
  destruct H as [d [bd cd]].
  exists d; split.
  apply trans_Runion_elim with (R_ << i).
  apply lt_subrel_le.
  exact bd.
  apply le_trans_eq_curly_trans.
  apply refl_trans_step.
  exact cd.
Qed.

Lemma X_top : 
  X top top ->
  confluent (Rfam_union R_).
Proof.
  intros Xtt.
  apply confluent_eq with (R_<<= top).
  split; intros a b [i Riab]; exists i.
  apply Riab.
  split.
  destruct (top_top i) as [Eit | Lit].
  right; rewrite Eit; apply (proj1 (proj1 oeq)).
  left; exact Lit.
  exact Riab.
  apply X_confluence; exact Xtt.
Qed.

(* Diagrams SS1, SS1_lt and SS2 for proving X *)

Lemma SS1 : 
  forall alpha: I,
  (forall alpha', L alpha' alpha -> X alpha' alpha') ->
  forall gamma,
  L gamma alpha ->
  confluent (R_<<= gamma).
Proof.
  intros alpha IH gamma Lga.
  apply X_confluence.
  apply IH.
  exact Lga.
Qed.

Lemma SS1_lt : 
  forall alpha: I,
  (forall alpha', L alpha' alpha -> X alpha' alpha') ->
  forall gamma,
  LE gamma alpha ->
  confluent (R_<< gamma).
Proof.
  destruct oeq as [[Erefl [Esymm Etrans]] [LinvE [Lirrefl Ltrans]]].
  intros alpha IH gamma LEga a b c Rab Rac.
  destruct (lt_red_lt Rab) as [[Egb Eab] | [Lbg [gamma' [Lg'g Rab']]]].
  rewrite <- Eab.
  exists c; split; [exact Rac | apply refl_trans_refl].
  destruct (lt_red_lt Rac) as [[Egb _] | [_ [gamma'' [Lg''g Rac'']]]].
  rewrite Egb in Lg'g.
  destruct (bot_lt Lg'g).
  destruct (max_label Lg'g Rab' Lg''g Rac'') as [m [Lmg [ab ac]]].
  assert (Lma := lt_le Lmg LEga).
  destruct (SS1 IH Lma ab ac) as [d [bd cd]].
  exists d; split;
  apply refl_trans_monotone with (R_<<= m).
  apply (red_incl_lt Lmg).
  exact bd.
  apply (red_incl_lt Lmg).
  exact cd.
Qed.

Lemma SS2 :
  forall alpha beta : I, 
  LE beta alpha ->
  (forall alpha' : I, L alpha' alpha -> X alpha' alpha') ->
  (forall gamma : I, L gamma beta -> X beta gamma) ->
  forall (n : nat),
  forall (a b c : A),
  (R_<< beta)* a c ->
  (curlyn beta n) a b ->
   exists d : A, (curlyn beta n) c d /\ (R_<< beta)* b d.
Proof.
  destruct oeq as [[Erefl [Esymm Etrans]] [LinvE [Lirrefl Ltrans]]].
  intros alpha beta LEba IH1 IH2.
  induction n as [|n IHn]; simpl; intros a b c ac ab.

  (* base case n = 0 *)
  rewrite <- ab.
  exists c; split; [reflexivity | exact ac].

  (* setting up the n = 1 subdiagram *)
  destruct ab as [a' [aa' a'b]].
  assert (dia : exists d', (R_<< beta)* a' d' /\ (~~> beta c d')).
  destruct aa' as [a0 [aa0 a0a']].

  (* MAPPING
     a----a0----a1----a'--...--b
     |    |           |        |
     |    |           |        |
     c----d0----d1----d'--...--d
  *)   

  destruct (SS1_lt IH1 LEba aa0 ac) as [d0 [a0d0 cd0]]. 
  (* finding gamma for a0d0 *)
  destruct (lt_red_lt a0d0) as [[Ebb Ea0d0]| [Lbb [gamma [Lgb Rg_a0d0]]]].
  exists a'; split; [apply refl_trans_refl | ].
  exists a0; split; [rewrite Ea0d0 | ]; trivial.
  (* applying IH2 *)
  destruct a0a' as [a1 [a0a1 a1a']].
  destruct (IH2 gamma Lgb a0 a1 a' d0 Rg_a0d0 a0a1 a1a') as [d' [a'd' d0d']].
  exists d'; split.
  (* a' -- d' *)
  apply trans_Runion_elim with (R_<<= gamma).
  apply red_incl_lt; exact Lgb.
  apply refl_trans_monotone with (R_ << beta(+)R_ <<= gamma).
  apply Runion_symm.
  exact a'd'.
  (* c -- d' *)
  destruct d0d' as [d1 [d0d1 d1d']].
  exists d1; split.
  apply refl_trans_trans with d0.
  exact cd0.
  apply refl_trans_monotone with (R_ << gamma).
  apply subrel_trans with (R_<<= gamma).
  apply lt_subrel_le.
  apply red_incl_lt; exact Lgb.
  exact d0d1.
  exact d1d'.
  
  (* using ind hypothesis *)
  destruct dia as [d' [a'd' cd']].
  destruct (IHn a' b d' a'd' a'b) as [d [d'd bd]].
  exists d; split; [ | exact bd].
  exists d'; split; [exact cd' | exact d'd].
Qed.

Lemma X_n_eq_1_beta'_eq_bottom :
  forall (alpha beta : I),
  LE beta alpha ->
  (forall alpha' : I, L alpha' alpha -> X alpha' alpha') -> 
  (forall alpha' : I, L alpha' beta -> X alpha alpha') ->
  (forall gamma : I, L gamma beta -> X beta gamma) ->
  forall (a b c : A),
  ((R_ alpha #) ; (R_ << alpha *)) a b ->
  ((R_ beta #) ; (R_ << beta *)) a c 
  ->
  exists d,
  ((R_ << beta *); (R_ alpha #); (R_ << alpha *)) c d /\
  ((R_ << alpha (+) R_ <<= beta) *) b d.
Proof.
  (* MAPPING
     a--------------b1-----b
     |    wdp       |  SS1 |
     c1---w1---w2---w  and |
     | SS1| X(a, <b) \ SS2 |
     c----d1--d2--d3--d4---d
  *)   

  destruct oeq as [[Erefl [Esymm Etrans]] [LinvE [Lirrefl Ltrans]]].
  intros alpha beta LEba Xaa Xaa' Xbg a b c [b1 [Rab1 Rb1b]] [c1 [Rac1 Rc1c]].

  (* First handle the case E beta bot *)
  destruct (bot_bot beta) as [Ebb | Lbb].
  assert (Ebb' : E beta bot).
  rewrite Ebb; apply Erefl.
  
  destruct Rac1 as [a c1 Rac1 | a ].
  (* Rac1 non-empty *)
  apply (bot_red_step Ebb') in Rac1.
  apply (bot_red_lt Ebb') in Rc1c.
  rewrite <- Rc1c; rewrite <- Rac1.
  exists b; split; [exists a; split; [ | exists b1; split] | ]; 
  try (apply refl_trans_refl).
  exact Rab1.
  apply Rb1b.
  (* Rac1 empty *)
  apply (bot_red_lt Ebb') in Rc1c.
  rewrite <- Rc1c.
  exists b; split; [exists a; split; [ | exists b1; split] | ]; 
  try (apply refl_trans_refl).
  exact Rab1.
  apply Rb1b.
  
  (* wdp diagram, joins in w.
     We have (R <<= alpha * ) b1 w in general,
     And also (R << alpha * ) b1 w if L beta alpha *)
  pose proof (wdp_refl LEba Rac1 Rab1) as [w [Rc1w [Rb1w wdpL]]].
  
  destruct Rc1w as [w1 [Rc1w1 [w2 [Rw1w2 Rw2w]]]].

  (* bottom left diagram, using SS1 *)
  assert (betaconf := SS1_lt Xaa LEba).
  destruct (betaconf c1 w1 c Rc1w1 Rc1c) as [d1 [Rw1d1 Rcd1]].

  (* subdiagram X(a, <b) *)
  destruct (lt_red_lt Rw1d1) as [[Ebb _] | [_ [gamma [Lgb Rgw1d1]]]].
  rewrite Ebb in Lbb; destruct (Lirrefl bot Lbb).
  assert (Lga := lt_le Lgb LEba).
  destruct (Xaa' gamma Lgb w1 w2 w d1 Rgw1d1 Rw1w2 Rw2w) as [d4 [Ruwd4 Rd1d4]].
  assert (Rwd4 : (R_ << alpha *) w d4).
  apply trans_Runion_elim with (R_<<= gamma).
  apply red_incl_lt; exact Lga.
  apply refl_trans_monotone with (R_ << alpha (+) R_ <<= gamma).
  apply Runion_symm.
  exact Ruwd4.

  (* destruct bottom reduction sequence completely,
     and transform gamma to beta *)
  destruct Rd1d4 as [d2 [Rgd1d2 [d3 [Rd2d3 Rd3d4]]]].
  assert (Rd1d2 : (R_ << beta *) d1 d2).
  apply refl_trans_monotone with (R_ << gamma).
  apply subrel_trans with (R_<<= gamma).
  apply lt_subrel_le.
  apply red_incl_lt; exact Lgb.
  exact Rgd1d2.

  (* rightmost diagram *)
  assert (concl : exists d,
                  ((R_ << alpha(+)R_ <<= beta) *) b d /\
                  (R_ << alpha *) d4 d).

  pose proof LEba as [Lba | Eba].
  
  (* case 1 : L beta alpha, applying SS1 *) 
  assert (LEaa : LE alpha alpha). 
  right; apply Erefl.
  assert (alphaconf := SS1_lt Xaa LEaa).
  assert (Rb1d4 := refl_trans_trans (wdpL Lba) (Rwd4)).
  destruct (alphaconf b1 d4 b Rb1d4 Rb1b) as [d [Rd4d Rbd]].
  exists d; split.
  apply refl_trans_monotone with (R_ << alpha).
  intros x y H; left; exact H.
  exact Rbd.
  exact Rd4d.

  (* case 2: E beta alpha, applying SS2 *)
  assert (Rb1d4_exi : exists k, curlyn beta k b1 d4).
  apply refl_trans_nfold.
  apply le_trans_eq_curly_trans.
  apply refl_trans_monotone with (R_ <<= alpha).
  apply (Rle_eq (Esymm beta alpha Eba)).
  apply refl_trans_trans with w.
  exact Rb1w.
  apply refl_trans_monotone with (R_ << alpha).
  apply lt_subrel_le.
  exact Rwd4.
  destruct Rb1d4_exi as [k Rb1d4].

  assert (Rb1b' : R_ << beta * b1 b).
  apply refl_trans_monotone with (R_ << alpha).
  apply (Rlt_eq (Esymm beta alpha Eba)).
  exact Rb1b.
  destruct (SS2 LEba Xaa Xbg k d4 Rb1b' Rb1d4) as [d [Rbd Rd4d]].
  exists d; split.
  apply refl_trans_monotone with (R_ <<= beta).
  intros x y xy; right; exact xy.
  apply le_trans_eq_curly_trans.
  apply refl_trans_nfold.
  exists k. 
  exact Rbd.
  apply refl_trans_monotone with (R_ << beta).
  apply (Rlt_eq Eba).
  exact Rd4d.
  
  (* finishing *)
  destruct concl as [d [Rbd Rd4d]].
  exists d; split.
  exists d2; split.
  apply refl_trans_trans with d1.
  exact Rcd1.
  exact Rd1d2.
  exists d3; split.
  exact Rd2d3.
  apply refl_trans_trans with d4.
  exact Rd3d4.
  exact Rd4d.
  exact Rbd.
Qed.

Definition X_n_eq_1_dia (alpha beta beta': I) :=
  forall (a b c : A),
  ((R_ alpha #) ; (R_ << alpha *)) a b ->
  ((R_ <<= beta' *) ; (R_ beta #) ; (R_ << beta *)) a c
  ->
  exists d : A,
  ((R_ << beta *) ; (R_ alpha #) ; (R_ << alpha *)) c d /\
  ((R_ << alpha (+) R_ <<= beta) *) b d.

Lemma X_n_eq_1 :
  forall (alpha beta beta' : I),
  LE beta alpha ->
  L beta' beta ->
  (forall alpha' : I, L alpha' alpha -> X alpha' alpha') -> 
  (forall alpha' : I, L alpha' beta -> X alpha alpha') ->
  (forall gamma : I, L gamma beta -> X beta gamma) ->
  (forall delta : I, L delta beta' -> X_n_eq_1_dia alpha beta delta) ->
  X_n_eq_1_dia alpha beta beta'.
Proof.
  destruct oeq as [[Erefl [Esymm Etrans]] [LinvE [Lirrefl Ltrans]]].
  intros alpha beta beta' LEba Lb'b Xaa Xaa' Xbg IH.
  intros a b c Rab Rac.
  pose proof Rab as [b1 [Rab1 Rb1b]].
  pose proof Rac as [c1 [Rac1 Rc1c]].
  pose proof Rc1c as [c2 [Rc1c2 Rc2c]].
  assert (Lb'a := lt_le Lb'b LEba).

  destruct (bot_bot beta') as [Eb'bot | Lbotb'].

  (* E beta' bot --> edge case *)
  apply (X_n_eq_1_beta'_eq_bottom LEba Xaa Xaa' Xbg Rab).
  assert (a_eq_c1 : a = c1).
  apply bot_red_le with beta'.
  rewrite Eb'bot; apply Erefl.
  exact Rac1.
  rewrite -> a_eq_c1.
  exact Rc1c.

  (* L bot beta' *)

  (* MAPPING
     a------b1------b
     |      Xab'    |
     c1---w1---w2---w
     |    |         |
     c2   x1        |
     |Xbb'|   IH b' |
     |    x2        |
     |    |         |
     c----d1--d2-d3-d
  *)

  (* Top diagram X(a, b') *)
  destruct (Xaa' beta' Lb'b a b1 b c1) as [w X_concl]; trivial.
  destruct X_concl as [Rbw [w1 [Rc1w1 [w2 [Rw1w2 Rw2w]]]]].

  (* Bottom left diagram X(b, b') *)
  destruct (lt_red_lt Rc1w1) as [[Eb'b _] | [_ [gamma [Lgb' Rgc1w1]]]].
  rewrite Eb'b in Lbotb'; destruct (Lirrefl bot Lbotb').
  assert (Lgb := Ltrans gamma beta' beta Lgb' Lb'b).
  destruct (Xbg gamma Lgb c1 c2 c w1 Rgc1w1 Rc1c2 Rc2c) as [d1 [Rcd1 Rw1d1]].

  (* bottom right diagram, IH beta' *)
  assert (Rw1w : ((R_ alpha #) ; (R_<< alpha)*) w1 w).
  exists w2; split; [exact Rw1w2 | exact Rw2w].
  assert (Rw1d1' : (R_ <<= gamma *; R_ beta #; R_ << beta *) w1 d1).
  destruct Rw1d1 as [x1 [Rw1x1 Rx1d1]].
  exists x1; split; [ | exact Rx1d1].
  apply refl_trans_monotone with (R_<< gamma).
  apply lt_subrel_le.
  exact Rw1x1.
  assert (IH_concl := IH gamma Lgb' w1 w d1 Rw1w Rw1d1').
  destruct IH_concl as [d [[d2 [Rd1d2 Rd2d]] Rwd]].
  
  (* Finishing *)
  exists d; split.
  exists d2; split.
  apply refl_trans_trans with d1.
  apply trans_Runion_elim with (R_ <<= gamma).
  apply (red_incl_lt Lgb).
  apply refl_trans_monotone with (R_ << beta (+) R_ <<= gamma).
  apply Runion_symm.
  exact Rcd1.
  exact Rd1d2.
  exact Rd2d.
  apply refl_trans_trans with w.
  apply refl_trans_monotone with ((R_ << alpha) (+) (R_ <<= beta')).
  intros x y [Rxy | Rxy]; [left; exact Rxy | ].
  right.
  apply lt_subrel_le.
  apply (red_incl_lt Lb'b).
  exact Rxy.
  exact Rbw.
  exact Rwd.
Qed.

Definition X_ind_step_dia (alpha beta : I) (n : nat) :=
  forall (a b c : A),
  ((R_ alpha #) ; (R_ << alpha *)) a b ->
  curlyn beta (S n) a c
  ->
  exists (d : A),
  ((R_ << beta *) ; (R_ alpha #) ; (R_ << alpha *)) c d /\
  ((R_ << alpha (+) R_ <<= beta) *) b d.
  
Lemma X_ind_step :
  forall (alpha beta : I),
  forall (n : nat),
  LE beta alpha ->
  (forall alpha' : I, L alpha' alpha -> X alpha' alpha') -> 
  (forall alpha' : I, L alpha' beta -> X alpha alpha') ->
  (forall gamma : I, L gamma beta -> X beta gamma) ->
  (forall beta' : I, L beta' beta -> X_n_eq_1_dia alpha beta beta') ->
  (n > 0 -> X_ind_step_dia alpha beta (pred n)) ->
  X_ind_step_dia alpha beta n.
Proof.
  destruct oeq as [[Erefl [Esymm Etrans]] [LinvE [Lirrefl Ltrans]]].
  intros alpha beta n LEba Xaa Xaa' Xbg base IH.
  intros a b c Rab Rac.
  pose proof Rab as [b1 [Rab1 Rb1b]].
  pose proof Rac as [c1 [Rac1 Rc1c]].

  (* MAPPING
     a-------------b1-------------b
     |    n = 1    |  SS1 and SS2 |
     c1----w1--w2--w3-------------w
     | SS2 |         IH n         |
     c-----d1------d2------d3-----d
  *)

  (* First handle the case E beta bot *)
  destruct (bot_bot beta) as [Ebb | Lbb].
  assert (Ebb' : E beta bot).
  rewrite Ebb; apply Erefl.
  assert (sub : subrel (~~> beta *) (@eq A)).
  apply subrel_trans with (R_<<= beta *).
  apply le_trans_eq_curly_trans.
  apply bot_red_le.
  exact Ebb'.
  assert (a_eq_c : a = c).
  apply sub.
  apply refl_trans_nfold; exists (S n); exact Rac.
  exists b; split; [ | apply refl_trans_refl].
  rewrite <- a_eq_c.
  exists a; split; [apply refl_trans_refl | exact Rab].

  (* top left, n = 1 diagram *)
  destruct Rac1 as [f [Raf Rfc1]].
  destruct (lt_red_lt Raf) as [[Ebb _] | [_ [beta' [Lb'b Rb'af]]]].
  rewrite Ebb in Lbb; destruct (Lirrefl bot Lbb).
  destruct (base beta' Lb'b a b1 c1) as [w3 [[w1 [Rc1w1 [w2 [Rw1w2 Rw2w3]]]] Rb1w3]].
  exists b1; split; [exact Rab1 | apply refl_trans_refl].
  exists f; split; [exact Rb'af | exact Rfc1].

  (* bottom left diagram, using SS2 *)
  destruct (SS2 LEba Xaa Xbg n c Rc1w1 Rc1c) as [d1 [Rw1d1 Rcd1]].

  (* top right diagram, using SS1 and SS2 *)
  assert (top_right : exists w, ((R_ << alpha)(+)(R_ <<= beta))* b w /\
                    (R_ << alpha *) w3 w).

  pose proof LEba as [Lba | Eba].
  (* L beta alpha, with SS1 *)
  assert (alphaconf := SS1_lt Xaa (or_intror (Erefl alpha))).
  destruct (alphaconf b1 b w3 Rb1b) as [w [Rbw Rw3w]].
  apply trans_Runion_elim with (R_<<= beta).
  apply (red_incl_lt Lba).
  apply refl_trans_monotone with ((R_ << alpha(+)R_ <<= beta)).
  apply Runion_symm.
  exact Rb1w3.
  exists w; split.
  apply refl_trans_monotone with (R_<< alpha).
  left; exact H.
  exact Rbw.
  exact Rw3w.
  (* E beta alpha, using SS2 *)
  (* label Rb1w3 with curlyn k for some k *)
  assert (Rb1w3' : R_ <<= beta * b1 w3).
  apply trans_Runion_elim with (R_ << alpha).
  apply subrel_trans with (R_<<= alpha).
  apply lt_subrel_le.
  apply (Rle_eq (Esymm beta alpha Eba)).
  exact Rb1w3.
  assert (exi_k : exists k, (curlyn beta k) b1 w3).
  apply refl_trans_nfold.
  apply le_trans_eq_curly_trans.
  exact Rb1w3'.
  destruct exi_k as [k Rkb1w3].

  assert (Rb1b' : (R_ << beta *) b1 b).
  apply refl_trans_monotone with (R_<< alpha).
  apply (Rlt_eq (Esymm beta alpha Eba)).
  exact Rb1b.

  destruct (SS2 LEba Xaa Xbg k w3 Rb1b' Rkb1w3) as [w [Rkbw Rw3w]].
  exists w; split.
  apply refl_trans_monotone with (R_<<= beta).
  intros x y; right; exact H.
  apply le_trans_eq_curly_trans.
  apply refl_trans_nfold.
  exists k; exact Rkbw.
  apply refl_trans_monotone with (R_<< beta).
  apply (Rlt_eq Eba).
  exact Rw3w.

  destruct top_right as [w [Rbw Rw3w]].

  (* Bottom IH n diagram *)
  destruct n.
  (* n = 0 *)
  assert (c1c : c = c1).
  destruct Rc1c; reflexivity.
  rewrite c1c.
  exists w; split.
  exists w1; split; [exact Rc1w1 | ].
  exists w2; split; [exact Rw1w2 | ].
  apply refl_trans_trans with w3; [exact Rw2w3 | exact Rw3w].
  exact Rbw.

  (* S n *)
  assert (notzero : S n > 0).
  generalize n; induction n0; [apply le_n | apply le_S; apply IHn0].

  destruct (IH notzero w1 w d1) as [d [[d2 [Rd1d2 Rd2d]] Rwd]].
  exists w2; split; [exact Rw1w2 | ].
  apply refl_trans_trans with w3; [exact Rw2w3 | exact Rw3w].
  exact Rw1d1.

  (* finishing up *)
  exists d; split.
  exists d2; split; [ | exact Rd2d].
  apply refl_trans_trans with d1; [exact Rcd1 | exact Rd1d2].
  apply refl_trans_trans with w; [exact Rbw | exact Rwd].
Qed.

Lemma Xeq :
  forall alpha alpha' beta,
  E alpha alpha' ->
  X alpha beta ->
  X alpha' beta.
Proof.
  destruct oeq as [[Erefl [Esymm Etrans]] [LinvE [Lirrefl Ltrans]]].
  intros alpha alpha' beta Eaa' Xab.
  intros a b' b c ac ab' b'b.

  assert (ab'' : (R_ alpha #) a b').
  destruct ab' as [a b' ab' | a].
  left; apply (REcongr Eaa') in ab'; exact ab'.
  right.
  assert (b'b' : R_<< alpha * b' b).
  apply refl_trans_monotone with (R_<< alpha').
  apply (Rlt_eq (Esymm alpha alpha' Eaa')).
  exact b'b.
  assert (H : exists d : A,
            ((R_ << alpha (+) R_ <<= beta) *) b d /\
            (R_ << beta *; R_ alpha #; R_ << alpha *) c d).
  apply (Xab a b').
  exact ac.
  exact ab''.
  exact b'b'.
  destruct H as [d [Rbd Rcd]].
  exists d; split.
  apply refl_trans_monotone with (R_ << alpha(+)R_ <<= beta).
  intros x y [Rxy | Rxy].
  left; apply (Rlt_eq Eaa'); trivial.
  right; trivial.
  exact Rbd.
  destruct Rcd as [x [Rcx [y [Rxy Ryd]]]].
  exists x; split; [trivial | ].
  exists y; split.
  destruct Rxy as [x y xy | x].
  left; apply (REcongr Eaa'); exact xy.
  right.
  apply refl_trans_monotone with (R_ << alpha).
  apply (Rlt_eq Eaa'); trivial.
  exact Ryd.
Qed.

Lemma X_inh : 
  forall alpha beta, 
  LE beta alpha ->
  X alpha beta.
Proof.
  destruct oeq as [[Erefl [Esymm Etrans]] [LinvE [Lirrefl Ltrans]]].

  set (P := fun alpha beta => 
            LE beta alpha ->
            (forall beta', L beta' beta -> X_n_eq_1_dia alpha beta beta') /\
            (forall n, X_ind_step_dia alpha beta n) /\
            X alpha beta).

  assert (XXX : forall alpha beta, P alpha beta).

  intros alpha.
  apply well_founded_induction_type with (1:=wfL) (P:=fun alpha => forall beta, P alpha beta).
  clear alpha.

  intros alpha IHalpha beta.
  apply well_founded_induction_type with (1:=wfL) (P:= fun beta => P alpha beta).
  clear beta.
  intros beta IHbeta LEba.

  assert (Xaa : forall alpha' : I, L alpha' alpha -> X alpha' alpha').
  intros alpha' H.
  apply (IHalpha alpha' H).
  right; apply Erefl.

  assert (Xab' : forall beta' : I, L beta' beta -> X alpha beta').
  intros beta' Lb'b.
  apply (IHbeta beta' Lb'b).
  left; apply (lt_le Lb'b LEba).

  assert (Xbg : forall gamma : I, L gamma beta -> X beta gamma).
  intros gamma Lgb.
  pose proof LEba as [Lba | Eba].
  apply (IHalpha beta).
  exact Lba.
  left; exact Lgb.
  apply Xeq with alpha.
  exact (Esymm beta alpha Eba).
  apply (IHbeta gamma).
  exact Lgb.
  left; apply (lt_le Lgb LEba).
  
  assert (base : forall beta' : I, L beta' beta -> X_n_eq_1_dia alpha beta beta').
  intros beta'.
  apply well_founded_induction_type with (1:=wfL) (P:= fun beta' => L beta' beta -> X_n_eq_1_dia alpha beta beta').
  clear beta'.
  intros beta' IHbeta' Lb'b.
  apply (X_n_eq_1 LEba Lb'b Xaa Xab' Xbg).
  intros delta Ldb'.
  apply IHbeta'.
  exact Ldb'.
  apply (Ltrans delta beta' beta Ldb' Lb'b).

  assert (ind_step : forall n : nat, X_ind_step_dia alpha beta n).
  intros n.
  induction n.
  apply (X_ind_step LEba Xaa Xab' Xbg base).
  intros zz; inversion zz.
  apply (X_ind_step LEba Xaa Xab' Xbg base).
  intros snz; apply IHn.

  split; [apply base | split; [apply ind_step|]].

  intros a b' b c ac ab' b'b.
  assert (trans_curly : subrel (R_ <<= beta *) (curly beta*)).
  apply le_trans_eq_curly_trans.
  destruct (proj1 (refl_trans_nfold (~~> beta)) a c (trans_curly a c ac)) as [n ac'].
  clear ac; rename ac' into ac.
  assert (ab : ((R_ alpha #) ; (R_ << alpha *)) a b).
  exists b'; split; trivial.
  destruct n.
  exists b; split; [apply refl_trans_refl | ].
  rewrite <- ac.
  exists a; split; [apply refl_trans_refl | trivial].
  destruct (ind_step n a b c ab ac) as [d [Rcd Rbd]].
  exists d; split; trivial.

  apply XXX.
Qed.

Theorem weak_diamond_property_implies_confluence :
  confluent (Rfam_union R_).
Proof.
destruct oeq as [[Erefl [_ _]] [_ [_ _]]].
apply X_top.
apply X_inh.
right.
apply Erefl.
Qed.

End weak_diamond_property.