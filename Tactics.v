Require Export List Arith Utf8 Program Setoid Classes.Morphisms NPeano.
Require Export Tactics.Common.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Local Open Scope list_scope.

Hint Extern 0 => match goal with H : False |- _ => destruct H end.
Hint Extern 0 => match goal with H : None = Some _ |- _ => inversion H end.
Hint Extern 0 => match goal with H : Some _ = None |- _ => inversion H end.
Hint Extern 0 => match goal with H : false = true |- _ => inversion H end.
Hint Extern 0 => match goal with H : true = false |- _ => inversion H end.
Hint Extern 0 => match goal with H0 : ?T, H1 : ?T -> False |- _ => destruct (H1 H0) end.
Hint Extern 0 => match goal with H0 : ?T, H1 : ~?T |- _ => destruct (H1 H0) end.
Hint Extern 0 => match goal with H : None = Some _ |- _ => inversion H end.
Hint Extern 0 => solve [ reflexivity ].
Hint Extern 0 => match goal with H : Forall _ (_ :: _) |- _ => inversion_clear H end.
Hint Extern 0 => match goal with H : ?x <> ?x |- _ => destruct (H eq_refl) end.
Hint Extern 0 => match goal with H : lt _ 0 |- _ => destruct (@lt_n_0 _ H) end.
Hint Extern 0 => match goal with |- appcontext[match ?E with end] => case E end.
Hint Resolve nil_cons.
Hint Extern 0 => match goal with H : S _ = 0 |- _ => destruct (Nat.neq_succ_0 _ H) end.
Hint Extern 0 => match goal with H : 0 = S _ |- _ => destruct (Nat.neq_0_succ _ H) end.
Hint Extern 0 => match goal with H : ?x < ?x |- _ => destruct (@lt_irrefl _ H) end.

Lemma eq_list_nil_dec {T} (l : list T) : {l = []} + {l <> []}.
Proof.
  destruct l; [ left; reflexivity | right; abstract inversion 1 ].
Defined.

Class Total {T} (R : relation T) := totality : forall x y, R x y \/ R y x.

Class Decidable (P : Prop) := decide : {P} + {~P}.

Arguments decide _ {_}.

Infix "∈" := List.In (at level 40, no associativity).

Section dec.
  Local Hint Extern 0 => apply partial_order_antisym.
  Local Hint Extern 2 => symmetry.

  Local Ltac t :=
    progress repeat (intro
                       || destruct_sig
                       || destruct_head_hnf @sumbool
                       || destruct_head_hnf @or
                       || destruct_head_hnf @and
                       || destruct_head_hnf @ex
                       || subst
                       || intro
                       || eauto
                       || split
                       || left
                       || right).


  Local Obligation Tactic := try abstract t.

  Global Instance in_decidable {A} `{H : forall x y : A, Decidable (x = y)}
         a (l : list A)
  : Decidable (a ∈ l)
    := in_dec H a l.

  Global Program Instance and_decidable `{a : Decidable A, b : Decidable B}
  : Decidable (A /\ B)
    := match a, b with
         | left a', left b' => left (conj a' b')
         | right a', _ => right _
         | _, right b' => right _
       end.
  Global Program Instance or_decidable `{a : Decidable A, b : Decidable B}
  : Decidable (A \/ B)
    := match a, b with
         | left a', _ => left (or_introl a')
         | _, left b' => left (or_intror b')
         | right a', right b' => right _
       end.
  Global Program Instance not_decidable `{a : Decidable A} : Decidable (~A)
    := match a with
         | left a' => right _
         | right a' => left _
       end.
  Fixpoint ex_in_list_decidable {A P}
         `{in_dec : forall (a : A) ls, Decidable (a ∈ ls)}
         `{P_dec : forall a : A, Decidable (P a)}
         (ls : list A)
  : Decidable (exists a, a ∈ ls /\ P a).
  Proof.
    refine match ls as ls return {exists a, a ∈ ls /\ P a} + {~exists a, a ∈ ls /\ P a} with
             | nil => right _
             | x::xs => match P_dec x with
                          | left Px => left (ex_intro _ x _)
                          | right H0 => match @ex_in_list_decidable A P in_dec P_dec xs with
                                          | left exa => left (match exa with
                                                                | ex_intro x Hx => ex_intro _ x _
                                                              end)
                                          | right H1 => right _
                                        end
                        end
           end;
    clear ex_in_list_decidable P_dec in_dec ls; abstract t.
  Defined.
  Global Existing Instance ex_in_list_decidable.

  Local Obligation Tactic :=
    try abstract (t; do 2 apply_hyp'; eauto).

  Global Program Instance eqv_partial_order_decidable
         `{@PartialOrder A eqA eqvA R preo}
         x y
         `{Proper _ (eqA ==> eqA ==> impl)%signature R}
         `{H0 : Decidable (R x y), H1 : Decidable (R y x)}
  : Decidable (eqA x y)
    := match H0, H1 with
         | left _, left _ => left _
         | right _, _ => right _
         | _, right _ => right _
       end.
End dec.

Instance le_total : Total le.
Proof.
  intros x y.
  destruct (le_lt_dec x y); [ left; assumption | right ].
  etransitivity; try eassumption; hnf; auto with arith.
Defined.

Lemma total_decidable_neg_flip `{Total T R, forall x y, Decidable (R x y)} x y
: ~R x y -> R y x.
Proof.
  intro HR.
  destruct (decide (R y x)); trivial.
  exfalso; destruct (totality x y); auto.
Qed.

Hint Extern 2 => match goal with H : ~?R ?x ?y |- _ => unique pose proof (@total_decidable_neg_flip _ R _ _ x y H); try clear H end.
