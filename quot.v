From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice.
From mathcomp Require Import seq fintype generic_quotient order.
From mathcomp.zify Require Import zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import all_algebra.
Local Open Scope ring_scope.

(* https://isabelle.in.tum.de/library/HOL/HOL/Nat.html#Nat.semiring_1_class.of_nat|const *)
Definition of_nat {R : semiRingType} (n : nat) : R := n%:R.

Local Close Scope ring_scope.

(* https://isabelle.in.tum.de/library/HOL/HOL/Int.html#Int.intrel|const *)
Definition intrel : rel (nat * nat) :=
  fun ab cd : nat * nat => ab.1 + cd.2 == cd.1 + ab.2.

Section intrel_quot.

Let intrel_refl : reflexive intrel.
Proof. by move=> ?; rewrite /intrel. Qed.

Let intrel_sym : symmetric intrel.
Proof. by move=> [a b] [c d]; rewrite /intrel/= eq_sym. Qed.

Let intrel_trans : transitive intrel.
Proof.
move=> [a b] [c d] [e f]; rewrite /intrel/= => /eqP cb /eqP af.
by rewrite -(eqn_add2l a) addnCA af addnCA cb addnCA.
Qed.

Canonical intrel_canonical :=
  EquivRel intrel intrel_refl intrel_sym intrel_trans.
(* NB: Abs_Integ = \pi_iint *)

Definition iint := {eq_quot intrel}%qT.

HB.instance Definition _ : EqQuotient _ intrel iint := EqQuotient.on iint.
HB.instance Definition _ := Choice.on iint.

Declare Scope iint_scope.
Delimit Scope iint_scope with iint.

Import GRing.Theory.

Section integers_form_a_semiring.
Local Open Scope quotient_scope.

Definition zero_int : iint := \pi_iint (0, 0).

Local Notation "0" := (zero_int) : iint_scope.

Definition one_int : iint := \pi_iint (1, 0).

Local Notation "1" := (one_int) : iint_scope.

Definition plus_int0 (a b : nat * nat) := (a.1 + b.1, a.2 + b.2).

Definition plus_int (a b : iint) : iint :=
  \pi_iint (plus_int0 (repr a) (repr b)).

Local Notation "a + b" := (plus_int a b) : iint_scope.

Definition uminus_int0 (a : nat * nat) := (a.2, a.1).

Definition uminus_int (a : iint) : iint := \pi_iint (uminus_int0 (repr a)).

Local Notation "- a" := (uminus_int a) : iint_scope.

Definition minus_int0 (a b : nat * nat) := (a.1 + b.2, a.2 + b.1).

Definition minus_int (a b : iint) : iint :=
  \pi_iint (minus_int0 (repr a) (repr b)).

Local Notation "a - b" := (minus_int a b) : iint_scope.

Definition times_int0 (a b : nat * nat) :=
  (a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1).

Definition times_int (a b : iint) : iint :=
  \pi_iint (times_int0 (repr a) (repr b)).

Local Notation "a * b" := (times_int a b) : iint_scope.

Local Open Scope iint_scope.

Lemma pi_addi : {morph \pi_iint : x y / plus_int0 x y >-> (x + y)%iint}.
Proof.
move=> x y.
have H u : repr (\pi_(iint) u) = u %[mod iint] by rewrite reprK.
rewrite /plus_int /plus_int0 /=.
apply/eqmodP => /=; rewrite /intrel.
rewrite addnACA.
have /eqmodP/eqP/= <- := H x.
have /eqmodP/eqP/= <- := H y.
by rewrite addnACA.
Qed.
(* NB: to be able to use piE *)
Canonical pi_addi_morph := PiMorph2 pi_addi.

Lemma pi_oppi : {morph \pi_iint : x / uminus_int0 x >-> (- x)%iint}.
Proof.
move=> x .
have H u : repr (\pi_(iint) u) = u %[mod iint] by rewrite reprK.
rewrite /uminus_int /uminus_int0 /=.
apply/eqmodP => /=; rewrite /intrel.
rewrite [eqbRHS]addnC.
have /eqmodP/eqP/= <- := H x.
by rewrite addnC.
Qed.
(* NB: to be able to use piE *)
Canonical pi_oppi_morph := PiMorph1 pi_oppi.

Lemma pi_subi : {morph \pi_iint : x y / minus_int0 x y >-> (x - y)%iint}.
Proof.
move=> x y.
have H u : repr (\pi_(iint) u) = u %[mod iint] by rewrite reprK.
rewrite /minus_int /minus_int0 /=.
apply/eqmodP => /=; rewrite /intrel.
rewrite addnACA.
have /eqmodP/eqP/= <- := H x.
rewrite (addnC y.2).
have /eqmodP/eqP/= -> := H y.
by rewrite (addnC y.1) addnACA.
Qed.
(* NB: to be able to use piE *)
Canonical pi_subi_morph := PiMorph2 pi_subi.

Lemma pi_muli : {morph \pi_iint : x y / times_int0 x y >-> (x * y)%iint}.
Proof.
move=> yz uv.
have H u : repr (\pi_(iint) u) = u %[mod iint] by rewrite reprK.
rewrite /times_int /times_int0 /=.
apply/eqmodP => /=; rewrite /intrel/=.
set w := (repr (\pi_(iint) yz)).1.
set x := (repr (\pi_(iint) yz)).2.
set s := (repr (\pi_(iint) uv)).1.
set t := (repr (\pi_(iint) uv)).2.
have /eqmodP/eqP/= := H yz; rewrite -/w -/x => H1.
have /eqmodP/eqP/= := H uv; rewrite -/s -/t => H2.
lia.
Qed.
(* NB: to be able to use piE *)
Canonical pi_muli_morph := PiMorph2 pi_muli.

From mathcomp Require Import ring.

Let addiA : associative plus_int.
Proof.
elim/quotW => -[a b]. elim/quotW => -[c d]. elim/quotW => -[e f].
rewrite !piE.
rewrite /plus_int0/=.
by rewrite !addnA.
Qed.

Let addiC : commutative plus_int.
Proof.
elim/quotW => -[a b]. elim/quotW => -[c d].
rewrite !piE.
rewrite /plus_int0/=.
by rewrite addnC (addnC b).
Qed.

Let add0i : left_id 0 plus_int.
Proof.
elim/quotW => -[a b].
rewrite !piE.
rewrite /plus_int0/=.
by rewrite !add0n.
Qed.

Let muliA : associative times_int.
Proof.
elim/quotW => -[a b]. elim/quotW => -[c d]. elim/quotW => -[e f].
rewrite !piE.
rewrite /times_int0/=.
rewrite !mulnDr.
rewrite !mulnA !addnA.
rewrite addnC !addnA -!mulnDl.
rewrite -addnA -mulnDl.
rewrite (addnC (b * d)%N).
rewrite (addnC _ (b * d * f)%N) !addnA -mulnDl.
rewrite -addnA -mulnDl.
by rewrite (addnC (b * d)%N).
Qed.

Let mul1i : left_id 1 times_int.
Proof.
elim/quotW => -[a b].
rewrite !piE.
rewrite /times_int0/=.
by rewrite !mul1n !mul0n !addn0.
Qed.

Let muli1 : right_id 1 times_int.
Proof.
elim/quotW => -[a b].
rewrite !piE.
rewrite /times_int0/=.
by rewrite !muln1 !muln0 !addn0.
Qed.

Let muliDl : left_distributive times_int plus_int.
Proof.
elim/quotW => -[a b]. elim/quotW => -[c d]. elim/quotW => -[e f].
rewrite !piE.
rewrite /times_int0/= /plus_int0/=.
by do 2 rewrite addnACA -!mulnDl.
Qed.

Let muliDr : right_distributive times_int plus_int.
Proof.
elim/quotW => -[a b]. elim/quotW => -[c d]. elim/quotW => -[e f].
rewrite !piE.
rewrite /times_int0/= /plus_int0/=.
by do 2 rewrite addnACA -!mulnDr.
Qed.

Let mul0i : left_zero 0 times_int.
Proof.
elim/quotW => -[a b].
rewrite !piE.
rewrite /times_int0/=.
by rewrite !mul0n !addn0.
Qed.

Let muli0 : right_zero 0 times_int.
Proof.
elim/quotW => -[a b].
rewrite !piE.
rewrite /times_int0/=.
by rewrite !muln0 !addn0.
Qed.

Let onei_neq0 : 1 != 0.
Proof. by rewrite !piE. Qed.

HB.instance Definition _ := @GRing.isSemiRing.Build iint 0 plus_int 1 times_int
  addiA addiC add0i muliA mul1i muli1 muliDl muliDr mul0i muli0 onei_neq0.

End integers_form_a_semiring.
(*Notation "0" := (zero_int) : iint_scope.
Notation "1" := (one_int) : iint_scope.
Notation "a + b" := (plus_int a b) : iint_scope.
Notation "a * b" := (times_int a b) : iint_scope.
Notation "a - b" := (minus_int a b) : iint_scope.
Notation "- a" := (uminus_int a) : iint_scope.*)

Section integers_form_a_semicomring.

Let muliC : commutative times_int.
Proof.
elim/quotW => -[a b]. elim/quotW => -[c d].
rewrite !piE.
rewrite /times_int0/=.
by rewrite 2!(mulnC a) 2!(mulnC b) (addnC (d * a)).
Qed.

HB.instance Definition _ := GRing.SemiRing_hasCommutativeMul.Build iint muliC.

End integers_form_a_semicomring.

Notation int := (@of_nat iint).

Section integers_form_a_zmodule.
Local Open Scope int_scope.
Local Open Scope quotient_scope.

Let addNi : left_inverse zero_int uminus_int plus_int.
Proof.
elim/quotW => -[a b].
rewrite !piE.
rewrite /plus_int0/=.
apply/eqmodP => /=.
by rewrite /intrel/= addn0 add0n addnC.
Qed.

HB.instance Definition _ := @GRing.Nmodule_isZmodule.Build iint uminus_int addNi.

End integers_form_a_zmodule.

Local Open Scope quotient_scope.
Lemma int_def (n : nat) : int n = \pi_iint (n, 0%N).
Proof.
elim: n => // n ih; rewrite /of_nat -natr1 -/(of_nat n) ih.
by rewrite !piE /plus_int0/= addn1 addn0.
Qed.

(* TODO: should be Lemma int_diff_cases (z : iint) : exists (m n : nat), z = (int m - int n)%iint. *)
Lemma int_diff_cases (m n : nat) : \pi_iint (m, n) = (int m - int n)%R.
Proof.
rewrite !int_def /intrel/=.
rewrite (_ : (m, n) = minus_int0 (m, 0) (n, 0))%N; last first.
  by rewrite /minus_int0/= addn0 add0n.
by rewrite piE.
Qed.
Local Close Scope quotient_scope.

Import Order.TTheory.
Local Open Scope order_scope.

Section integers_are_ordered.
Local Open Scope int_scope.
Local Open Scope quotient_scope.

Definition less_eq_int0 (a b : nat * nat) := (a.1 + b.2 <= b.1 + a.2)%N.

Definition less_eq_int (a b : iint) := less_eq_int0 (repr a) (repr b).

Local Notation "a <= b" := (less_eq_int a b).

Definition less_int0 (a b : nat * nat) := (a.1 + b.2 < b.1 + a.2)%N.

Definition less_int (a b : iint) := less_int0 (repr a) (repr b).

Local Notation "a < b" := (less_int a b).

Let lt_def (a b : iint) : (a < b) = (b != a) && (a <= b).
Proof.
rewrite /less_int /less_eq_int /less_int0 /less_eq_int0.
have [/= <-|ba/=] := eqVneq b a; first by rewrite ltnn.
rewrite ltn_neqAle andbC andb_idr// => _.
apply: contra ba => /eqP ba; rewrite -(reprK b) -(reprK a).
by apply/eqP/eqmodP => /=; rewrite /intrel; exact/eqP.
Qed.

Let le_refl : reflexive less_eq_int.
Proof. by move=> a; rewrite /less_eq_int/= /less_eq_int0. Qed.

Let le_anti : antisymmetric less_eq_int.
Proof.
move=> a b.
rewrite /less_eq_int/= /less_eq_int0 => /andP[ab ba].
rewrite -(reprK a) -(reprK b); apply/eqmodP => /=.
by rewrite /intrel eqn_leq ab ba.
Qed.

Let le_trans : transitive less_eq_int.
Proof.
move=> a b c; rewrite /less_eq_int/= /less_eq_int0 => H1 H2.
rewrite -(leq_add2l ((repr a).2)).
rewrite addnCA addnA.
apply (@leq_trans ((repr a).1 + (repr b).2 + (repr c).2)%N).
  by rewrite leq_add2r.
rewrite -addnA addnCA.
by rewrite [leqRHS]addnA [leqRHS]addnC leq_add2l [leqRHS]addnC.
Qed.

HB.instance Definition _ := @Order.isPOrder.Build ring_display iint
  less_eq_int less_int lt_def le_refl le_anti le_trans.

End integers_are_ordered.

Section integers_are_lattice.
Local Open Scope int_scope.
Local Open Scope quotient_scope.

Definition iinf (a b : iint) := if a <= b then a else b.

Definition isup (a b : iint) := if a <= b then b else a.

Let meetP x y z : (x <= iinf y z) = (x <= y) && (x <= z).
Proof.
rewrite /iinf; case: ifPn => yz.
  by rewrite andb_idr// => /le_trans; apply.
rewrite andb_idl// => /le_trans; apply.
move: yz.
rewrite /Order.le/= /less_eq_int /less_eq_int0/=.
by rewrite -ltnNge => /ltnW.
Qed.

Let joinP x y z : (isup x y <= z) = (x <= z) && (y <= z).
Proof.
rewrite /isup; case: ifPn => xy.
  by rewrite andb_idl//; apply: le_trans.
rewrite andb_idr//; apply: le_trans.
move: xy.
rewrite /Order.le/= /less_eq_int /less_eq_int0/=.
by rewrite -ltnNge => /ltnW.
Qed.

HB.instance Definition _ := @Order.POrder_MeetJoin_isLattice.Build _
  iint iinf isup meetP joinP.

End integers_are_lattice.

Section integers_are_total.

Let le_total : total (<=%O : rel iint).
Proof.
move=> a b.
rewrite /Order.le/= /less_eq_int /less_eq_int0.
exact: leq_total.
Qed.

HB.instance Definition _ := Order.Lattice_isTotal.Build
  _ iint le_total.

End integers_are_total.

Lemma ordered_cancel_ab_semigroup_add (i j k : iint) :
  (i <= j -> k + i <= k + j)%R.
Proof.
elim/quotW : i => -[a b/=].
elim/quotW : j => -[c d/=].
elim/quotW : k => -[e f/=].
rewrite !piE.
rewrite /plus_int0/=.
move=> H.
rewrite /Order.le/= /less_eq_int/= /less_eq_int0/=.
have H1 u : repr (\pi_(iint) u) = u %[mod iint]%qT by rewrite reprK.
have /eqmodP/eqP/= H1' := H1 (e + a, f + b).
rewrite -(leq_add2r (f + b)).
rewrite addnAC.
rewrite {}H1'.
rewrite [leqLHS]addnAC.
rewrite [leqRHS](addnC _ (f + b)).
rewrite !addnA leq_add2r.
have /eqmodP/eqP/= H1'' := H1 (e + c, f + d).
rewrite -(leq_add2r (e + c)).
rewrite -addnA.


Abort.

Section iint_hasmulinverse.

Definition uniti := [qualify a n : iint | (n == 1) || (n == -1)]%R.

Definition invi (z : iint) := z.

Let mulVi_subproof : {in uniti, left_inverse 1%R invi *%R}.
Proof.
move=> z; rewrite qualifE => /orP[|] /eqP ->.
  by rewrite /invi mulr1.
by rewrite /invi mulrN1 opprK.
Qed.

Let mulin_eq1 (m : iint) (n : nat) : (m * int n == 1)%R = (m == 1)%R && (n == 1)%R.
Proof.
elim/quotW : m => -[a b/=].
rewrite int_diff_cases.
move: n => [|[|n]].
- by rewrite mulr0 eq_sym oner_eq0 andbC eq_sym oner_eq0.
- by rewrite (_ : of_nat 1 = 1%R)// mulr1 eqxx andbT.
- have [ba|] := leqP b a.
  rewrite /of_nat -natrB// -natrM.
Admitted.

Let unitiP_subproof : forall x y : iint, (y * x = 1)%R -> x \is a uniti.
Proof.
move=> x y; rewrite qualifE => yx1.
rewrite -(reprK x)/=.
rewrite !piE/= /intrel/= addn0 add0n.
move: yx1; rewrite /GRing.mul/= /times_int/= piE/= /times_int0.
move/eqmodP => /=; rewrite /intrel/= addn0 => /eqP.
set c := (repr y).1.
set d := (repr y).2.
set a := (repr x).1.
set b := (repr x).2.
move=> H.
suff: (a = 1 + b) \/ (a + 1 = b).
  admit.
Admitted.

Let invi_out_subproof : {in [predC uniti], invi =1 id}.
Proof. by move=> x _. Qed.

HB.instance Definition _ := GRing.ComRing_hasMulInverse.Build iint mulVi_subproof
  unitiP_subproof invi_out_subproof.

End iint_hasmulinverse.

Section iint_idomain.

Let muli_eq0_subproof : GRing.integral_domain_axiom iint.
Proof.
move=> x y.
rewrite /GRing.mul.
rewrite /=.
rewrite /times_int.
Admitted.

HB.instance Definition _ :=
  @GRing.ComUnitRing_isIntegral.Build iint muli_eq0_subproof.

End iint_idomain.

(* https://isabelle.in.tum.de/library/HOL/HOL/Rat.html#Rat.rat|type *)
Definition ratrel : rel (iint * iint) :=
  fun ab cd => [&& ab.2 != 0, cd.2 != 0 & ab.1 * cd.2 == cd.1 * ab.2]%R.

Definition rat' := { x : iint * iint | ratrel x x }.

Definition from_rat' (x : rat') : iint * iint := let (x, _) := x in x.

Definition ratrel' : rel rat' := fun a b => ratrel (from_rat' a) (from_rat' b).

Section ratrel_quotient.

Let ratrel'_refl : reflexive ratrel'.
Proof. by move=> [a b]; rewrite /ratrel'/=. Qed.

Let ratrel'_sym : symmetric ratrel'.
Proof.
move=> [a Ha] [b Hb]; rewrite /ratrel'/=.
rewrite /ratrel in Ha Hb *.
move/and3P : Ha => [-> _ _] /=.
move/and3P : Hb => [-> _ _] /=.
by rewrite eq_sym.
Qed.

Let ratrel'_trans : transitive ratrel'.
Proof.
move=> [a Ha] [b Hb] [c Hc]; rewrite /ratrel'/=.
rewrite /ratrel in Ha Hb *.
move/and3P : Ha => [a0 _ _] /=.
move/and3P : Hb => [b0 _ _] /=.
move/and3P : Hc => [c0 _ _] /=.
rewrite a0 b0 c0/=.
move=> /eqP Ha /eqP Hb; apply/eqP.
suff: (b.1 * a.2 * c.2)%R = (c.1 * a.2 * b.2)%R.
  move=> suf.
  apply/(mulfI a0).
  by rewrite mulrCA mulrA suf -mulrA mulrCA.
by rewrite {}Ha -{}Hb mulrAC.
Qed.

Canonical ratrel_canonical :=
  EquivRel ratrel' ratrel'_refl ratrel'_sym ratrel'_trans.

End ratrel_quotient.

Definition irat := {eq_quot ratrel'}%qT.

HB.instance Definition _ : EqQuotient _ ratrel' irat := EqQuotient.on irat.
(*HB.instance Definition _ := Choice.on irat.*)

Declare Scope irat_scope.
Delimit Scope irat_scope with irat.

(* https://isabelle.in.tum.de/library/HOL/HOL/Real.html#Real.real|type *)
