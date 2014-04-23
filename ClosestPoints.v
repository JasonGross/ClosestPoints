(** * 1-D Closest Point Algorithm *)
Require Import List Ascii String Arith NPeano Sorted Program Setoid FMapAVL Wf Wf_nat Program Recdef Div2 Even NArith Classes.Morphisms.
Require Import Utf8.

Set Implicit Arguments.
Generalizable All Variables.

Local Open Scope list_scope.
Local Open Scope string_scope.

(** ** Helper tactics *)
(** We have some convience tactics. *)
(** find the head of the given expression *)
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

(** given a [matcher] that succeeds on some hypotheses and fails on
    others, destruct any matching hypotheses, and then execute [tac]
    after each [destruct].

    The [tac] part exists so that you can, e.g., [simpl in *], to
    speed things up. *)
Ltac destruct_all_matches_then matcher tac :=
  repeat match goal with
           | [ H : ?T |- _ ] => matcher T; destruct H; tac
         end.

Ltac destruct_all_matches matcher := destruct_all_matches_then matcher ltac:(simpl in *).
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

(* matches anything whose type has a [T] in it *)
Ltac destruct_type_matcher T HT :=
  match HT with
    | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).
Ltac destruct_type' T := destruct_all_matches' ltac:(destruct_type_matcher T).

Ltac destruct_head_matcher T HT :=
  match head HT with
    | T => idtac
  end.
Ltac destruct_head T := destruct_all_matches ltac:(destruct_head_matcher T).
Ltac destruct_head' T := destruct_all_matches' ltac:(destruct_head_matcher T).

Ltac destruct_head_hnf_matcher T HT :=
  match head_hnf HT with
    | T => idtac
  end.
Ltac destruct_head_hnf T := destruct_all_matches ltac:(destruct_head_hnf_matcher T).
Ltac destruct_head_hnf' T := destruct_all_matches' ltac:(destruct_head_hnf_matcher T).

Ltac destruct_sig_matcher HT :=
  match eval hnf in HT with
    | ex _ => idtac
    | ex2 _ _ => idtac
    | sig _ => idtac
    | sig2 _ _ => idtac
    | sigT _ => idtac
    | sigT2 _ _ => idtac
    | and _ _ => idtac
    | prod _ _ => idtac
  end.
Ltac destruct_sig := destruct_all_matches destruct_sig_matcher.
Ltac destruct_sig' := destruct_all_matches' destruct_sig_matcher.

Ltac destruct_all_hypotheses := destruct_all_matches ltac:(fun HT =>
  destruct_sig_matcher HT || destruct_sig_matcher HT
).

(** if progress can be made by [exists _], but it doesn't matter what
    fills in the [_], assume that something exists, and leave the two
    goals of finding a member of the apropriate type, and proving that
    all members of the appropriate type prove the goal *)
Ltac destruct_exists' T := cut T; try (let H := fresh in intro H; exists H).
Ltac destruct_exists := destruct_head_hnf @sigT;
  match goal with
(*    | [ |- @sig ?T _ ] => destruct_exists' T*)
    | [ |- @sigT ?T _ ] => destruct_exists' T
(*    | [ |- @sig2 ?T _ _ ] => destruct_exists' T*)
    | [ |- @sigT2 ?T _ _ ] => destruct_exists' T
  end.

(** fail if [x] is a function application, a dependent product ([fun _
    => _]), or a sigma type ([forall _, _]) *)
Ltac atomic x :=
  match x with
    | ?f _ => fail 1 x "is not atomic (application)"
    | (fun _ => _) => fail 1 x "is not atomic (fun)"
    | forall _, _ => fail 1 x "is not atomic (forall)"
    | _ => is_fix x; fail 1 x "is not atomic (fix)"
    | _ => idtac
  end.

(** [destruct] discriminees of [match]es, but only if they satisfy [tac] (e.g., [atomic] *)
Ltac destruct_in_match_if' tac :=
  match goal with
    | [ |- appcontext[match ?D with _ => _ end] ] => tac D; destruct D
  end.
Ltac destruct_in_match_if tac := repeat destruct_in_match_if' tac.

(** [destruct] things in [if]s *)
Ltac tac_if' tac :=
  match goal with
    | [ |- context[if ?a then _ else _] ] => tac a
  end.
Ltac tac_if tac := repeat tac_if' tac.
Ltac case_eq_if' := tac_if' case_eq.
Ltac case_eq_if := tac_if case_eq.

Ltac do_with_hyp tac :=
  match goal with
    | [ H : _ |- _ ] => tac H
  end.

Ltac rewrite_hyp' := do_with_hyp ltac:(fun H => rewrite H).
Ltac rewrite_hyp := repeat rewrite_hyp'.
Ltac rewrite_rev_hyp' := do_with_hyp ltac:(fun H => rewrite <- H).
Ltac rewrite_rev_hyp := repeat rewrite_rev_hyp'.

Ltac setoid_rewrite_hyp' := do_with_hyp ltac:(fun H => setoid_rewrite H).
Ltac setoid_rewrite_hyp := repeat setoid_rewrite_hyp'.
Ltac setoid_rewrite_rev_hyp' := do_with_hyp ltac:(fun H => setoid_rewrite <- H).
Ltac setoid_rewrite_rev_hyp := repeat setoid_rewrite_rev_hyp'.

Ltac apply_hyp' := do_with_hyp ltac:(fun H => apply H).
Ltac apply_hyp := repeat apply_hyp'.
Ltac eapply_hyp' := do_with_hyp ltac:(fun H => eapply H).
Ltac eapply_hyp := repeat eapply_hyp'.

(* [pose proof defn], but only if no hypothesis of the same type exists.
   most useful for proofs of a proposition *)
Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
    | [ H : T |- _ ] => fail 1
    | _ => pose proof defn
  end.

(** [pose defn], but only if that hypothesis doesn't exist *)
Tactic Notation "unique" "pose" constr(defn) :=
  match goal with
    | [ H := defn |- _ ] => fail 1
    | _ => pose defn
  end.

(** try to specialize all hypotheses with all other hypotheses.  This
    includes [specialize (H x)] where [H x] requires a coercion from
    the type of [H] to Funclass. *)
Ltac specialize_all_ways :=
  repeat match goal with
           | [ x : ?T, H : _ |- _ ] => unique pose proof (H x)
         end.

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
Hint Extern 0 => match goal with |- appcontext[match ?E with end] => destruct E end.
Hint Resolve nil_cons.

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

  Local Ltac t' :=
    progress repeat (intro
                       || destruct_sig
                       || destruct_head_hnf @sumbool
                       || destruct_head_hnf @or
                       || destruct_head_hnf @and
                       || destruct_head_hnf @ex
                       || subst
                       || intro
                       || eauto).

 Local Ltac t :=
    first [ abstract t'
          | left; abstract t'
          | right; abstract t'
          | t'; try t ].

  Local Obligation Tactic := try solve [ t ].

  Global Instance in_decidable {A} `{H : forall x y : A, Decidable (x = y)}
         a (l : list A)
  : Decidable (a ∈ l)
    := in_dec H a l.

  Global Program Instance and_decidable `{Decidable A, Decidable B}
  : Decidable (A /\ B).
  Global Program Instance or_decidable `{Decidable A, Decidable B}
  : Decidable (A \/ B).
  Global Program Instance not_decidable `{Decidable A} : Decidable (~A).
  Global Program Instance ex_in_list_decidable {A P}
         (ls : list A)
         `{forall (a : A) ls, Decidable (a ∈ ls)}
         `{forall a : A, Decidable (P a)}
  : Decidable (exists a, a ∈ ls /\ P a).
  Next Obligation.
    induction ls; t.
    specialize_all_ways; t.
  Defined.

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

(** ** Motivation *)
(** "When doing formal program verification, take the simplest
     non-trivial relevant example.  Then take a simpler example, and
     formalize that." -- paraphrase of Adam Chlipala on best practices
     in program synthesis and verification *)

(** We implement a simpler version of the recursive
    closest-points-in-a-plane algorithm from 6.850 Lecture 1.  In
    particular, we consider the 1-D version of the algorithm (which
    doesn't actually buy us any speed over sorting the list). *)

(** First, we implement a brute force check algorithm. *)

(** Take the minimum of two things which might be [nat]s. *)
Definition option_f {A} (f : A -> A -> A) : option A -> option A -> option A
  := fun a b => match a, b with
                  | None, _ => b
                  | _, None => a
                  | Some a, Some b => Some (f a b)
                end.

(** The distance between two points is the maximum of the two
    differences; in Coq, we have that [a - b = 0] if [b ≥ a]. *)
Definition abs_minus (x y : nat) :=
  if le_dec x y then y - x else x - y.

Notation "∥' x -- y '∥" := (abs_minus x y) : nat_scope.

(*(** We spec out what the algorithm does, functionally; it returns the
    smallest distance between distinct points.  If the list has not
    enough distinct points, we do not require anything at all. *)
Definition points_are_distinct_and_in_list (pts : list nat) (min_pts : nat * nat) : Prop
  := fst min_pts <> snd min_pts /\ List.In (fst min_pts) pts /\ List.In (snd min_pts) pts.*)

Delimit Scope dec_scope with dec.
Infix "<=" := le_lt_dec : dec_scope.
Infix "≤" := le_lt_dec : dec_scope.
Infix "=" := eq_nat_dec : dec_scope.

(*Fixpoint list_has_enough_distinct_points (pts : list nat) : Prop
  := match pts with
       | nil => False
       | _::nil => False
       | x::(y::zs) as pts'
         => if (x = y)%dec
            then list_has_enough_distinct_points pts'
            else True
     end.

Definition is_min_dist_points_helper (pts : list nat) (pt1 pt2 : nat) : Prop
  := List.Forall (fun pt => List.Forall (fun pt' => if (pt = pt')%dec
                                                    then True
                                                    else ∥' pt1 -- pt2 '∥ ≤ ∥' pt -- pt' '∥)
                                        pts)
                 pts.

Definition is_min_dist_points (pts : list nat) (min_pts : option (nat * nat)) : Prop
  := NoDup pts
     -> match pts, min_pts with
          | nil, _ => True
          | _::nil, _ => True
          | pts, None => False
          | pts, Some (pt1, pt2) => is_min_dist_points_helper pts pt1 pt2
        end.*)

(** We implement the brute force algorithm as a sanity check. *)
Fixpoint min_dist_pts_brute_force (pts : list nat) : option (nat * nat)
  := match pts with
       | nil => None
       | pt::pts' => fold_right (option_f
                                   (fun pts1 pts2 => if (∥' fst pts1 -- snd pts1 '∥ ≤ ∥' fst pts2 -- snd pts2 '∥)%dec
                                                     then pts1
                                                     else pts2))
                                (min_dist_pts_brute_force pts')
                                (map (fun pt' => if (pt = pt')%dec then None else Some (pt, pt'))
                                     pts')
     end.

Definition min_dist_brute_force (pts : list nat) : option nat :=
  match min_dist_pts_brute_force pts with
    | None => None
    | Some (p, q) => Some ∥' p -- q '∥
  end.

(** Sanity check *)
Eval compute in min_dist_pts_brute_force [1; 4; 5; 9].
(**
<<
     = Some (4, 5)
     : option (nat * nat)
>> *)
Eval compute in min_dist_brute_force [1; 4; 5; 9].
(**
<<
     = Some 1
     : option nat
>> *)


(*Lemma min_dist_pts_brute_force_correct (pts : list nat)
: is_min_dist_points pts (min_dist_pts_brute_force pts).
Proof.
  induction pts as [|? pts];
  [ | induction pts ];
  try solve [ simpl in *; repeat intro; intuition eauto ].
  simpl.
  intro.
  intro.
  intros.
  Focus 2.
  intro.
  destruct pts.
  intuition eauto.
  simpl.
  simpl in *.
  case_eq (min_dist_pts_brute_force pts).
  Focus 2.
  intro H.

  simpl.
  erewrite IHpts by eassumption.
  intros.

  destruct pts; simpl in *; eauto.
  case_eq_if; simpl in *.

  simpl in *.
  simpl in *.
  intros.
  simpl in *.
  intuition eauto.
  intuition eauto.
  simpl in *.
  intro.
  simpl in *.
  intro H.
  simpl in *.
  hnf.
  induction pts; try reflexivity.
  destruct pts; try reflexivity.
  destruct pts; try reflexivity.
  simpl in *.
  case_eq_if; eauto.
  simpl; intros.
  split.
  hnf; simpl.
  intuition eauto.
*)

(** Now we implement the axtual algorithm. *)

(** We parameterize over a type of points. *)
(** A [Point] is a [Type] together with a type of distances between points. *)
Module Type Point.
  Axiom t : Type.
  Axiom distT : Type.
  Axiom dist_le : distT -> distT -> Prop.
  Axiom get_dist : t -> t -> distT.
  Axiom x_le : t -> t -> Prop.
  Context `{x_le_dec : forall x y, Decidable (x_le x y),
              dist_le_dec : forall x y, Decidable (dist_le x y)}.

  Axiom point_in_strip_close_enough : t -> distT -> t -> bool.

  Axiom min_dist : distT -> distT -> distT.

  Context `{x_le_preo : PreOrder _ x_le, dist_le_preo : PreOrder _ dist_le}.
  Context `{x_le_paro : @PartialOrder _ eq _ x_le _, dist_le_paro : @PartialOrder _ eq _ dist_le _}.
  Context `{x_le_total : Total _ x_le, dist_le_total : Total _ dist_le}.

  Module Import Notations.
    Delimit Scope dist_scope with dist.
    Delimit Scope dec_dist_scope with dec_dist.

    Infix "<=" := x_le : type_scope.
    Infix "<=" := x_le_dec : dec_scope.
    Infix "<=" := dist_le : dist_scope.
    Infix "<=" := dist_le_dec : dec_dist_scope.

    Infix "≤" := x_le : type_scope.
    Infix "≤" := x_le_dec : dec_scope.
    Infix "≤" := dist_le : dist_scope.
    Infix "≤" := dist_le_dec : dec_dist_scope.

    Notation "∥' x -- y '∥" := (get_dist x y).
  End Notations.
End Point.

(** Given a boolean relation, we can find the [f]-most element of a list. *)
Definition get_func_bool {T} (f : T -> T -> bool) (*H : forall x y z, f x y = true -> f y z = true -> f x z = true*)
           (ls : list T)
: ls <> [] -> T
  := match ls with
       | [] => fun H => match H eq_refl : False with end
       | x::xs => fun _ => fold_right (fun acc pt => if (f acc pt) then acc else pt)
                                      x
                                      xs
     end.

Program Definition get_func {T} {R} `{f : forall x y : T, Decidable (R x y)} (*`{Transitive _ R}*) (ls : list T)
: ls <> [] -> T
  := @get_func_bool _ (fun x y => if f x y then true else false) (*_*) ls.
(*Next Obligation.
  abstract (
      destruct (f x y), (f y z), (f x z); hnf in *; firstorder eauto
    ).
Defined.*)

Section spec_get_func.
  Local Hint Extern 1 => intros; etransitivity; eassumption.
  Local Hint Extern 1 => eapply Forall_impl; [ | eassumption ].
  Local Hint Extern 3 => progress case_eq_if.
  Local Hint Constructors Forall.

  Lemma spec_rel_get_func {T} {R}
        `{forall x y : T, Decidable (R x y)}
        `{PartialOrder _ eq R, Total _ R}
        (ls : list T)
        (Hls : ls <> [])
  : List.Forall (fun elem => R (get_func Hls) elem) ls.
  Proof.
    destruct ls; auto; simpl.
    induction ls; auto;
    try solve [ do 2 (reflexivity || constructor) ].
    specialize (IHls (fun H => nil_cons (eq_sym H))).
    constructor; simpl.
    { eauto. }
    { constructor; eauto. }
  Qed.

  Lemma spec_in_get_func {T} {R}
        `{forall x y : T, Decidable (R x y)}
        `{PartialOrder _ eq R, Total _ R}
        (ls : list T)
        (Hls : ls <> [])
  : get_func Hls ∈ ls.
  Proof.
    destruct ls; eauto.
    simpl; clear Hls.
    induction ls; try solve [ intuition ].
    destruct_head or; simpl in *;
    rewrite_rev_hyp;
    case_eq_if;
    try solve [ intuition ].
  Qed.
End spec_get_func.

Module Type Strip (point : Point).
  Import point.Notations.

  Axiom get_closest_points_in_strip
  : forall (median : point.t)
           (pre_closest_pair : point.t * point.t)
           (strip : list point.t),
      point.t * point.t.

  Section correct.
    Context (median : point.t)
            (pre_closest_pair : point.t * point.t)
            (strip : list point.t).

    Let post_closest_pair := get_closest_points_in_strip median pre_closest_pair strip.

    Axiom get_closest_points_in_strip_closer
    : (∥' fst post_closest_pair -- snd post_closest_pair '∥
        ≤ ∥' fst pre_closest_pair -- snd pre_closest_pair '∥)%dist.

    (*Axiom get_closest_points_in_strip_closest
    : List.(∥' fst post_closest_pair -- snd post_closest_pair '∥
        ≤ ∥' fst pre_closest_pair -- snd pre_closest_pair '∥)%dist.

    Axiom get_closest_points_in_strip_in_strip
    : (∥' fst post_closest_pair -- snd post_closest_pair '∥
        ≤ ∥' fst pre_closest_pair -- snd pre_closest_pair '∥)%dist.*)
  End correct.
End Strip.

(** We can find the minimum or maximum of a list of points. *)
Module MidStrip1D (point : Point) <: Strip point.
  Import point.Notations.

  Definition get_left_most
  : forall ls : list point.t, ls <> [] -> point.t
    := let _ := point.x_le_dec in get_func.

  Definition get_right_most
  : forall ls : list point.t, ls <> [] -> point.t
    := (*let _ := point.x_le_preo in *)@get_func _ (flip point.x_le) (fun x y => point.x_le_dec y x) (*_*).

  (** Given two strips, we can find the right-most left point and
      left-most right point.  FIXME: Note: We don't handle duplicates correctly. *)
  Definition right_most_left_most (ls_left ls_right : list point.t)
             (H_left : ls_left <> []) (H_right : ls_right <> [])
  : point.t * point.t
    := (get_right_most H_left, get_left_most H_right).

  Local Ltac do_induct ls :=
    induction ls; simpl in *; intros; eauto;
    case_eq_if; intros; eauto;
    destruct_head or; repeat subst; eauto.

  (** We can also do it by filtering a single strip *)
  Program Definition right_most_left_most_from_median (ls : list point.t)
             (median : point.t)
             (H_left : exists pt, pt ∈ ls /\ pt ≤ median)
             (H_right : exists pt, pt ∈ ls /\ ~pt ≤ median)
  : point.t * point.t
    := @right_most_left_most
         (filter (fun pt => if (pt ≤ median)%dec then true else false) ls)
         (filter (fun pt => if (pt ≤ median)%dec then false else true) ls)
         _
         _.
  Next Obligation.
    match goal with
      | [ H : point.x_le ?x _ |- _ ] => generalize dependent x; clear
    end.
    do_induct ls.
  Qed.
  Next Obligation.
    match goal with
      | [ H : not (point.x_le ?x _) |- _ ] => generalize dependent x; clear
    end.
    do_induct ls.
  Qed.

  Definition get_closest_points_in_strip
          (median : point.t)
          (pre_closest_pair : point.t * point.t)
          (strip : list point.t)
  : point.t * point.t
    := let _ := point.x_le_preo in
       let _ := point.x_le_paro in
       let _ := point.x_le_dec in
       match (_ : Decidable (exists pt, pt ∈ strip /\ pt ≤ median)),
             (_ : Decidable (exists pt, pt ∈ strip /\ ~pt ≤ median)) with
         | left pf1, left pf2
           => let closest_in_strip := @right_most_left_most_from_median strip median pf1 pf2
              in if (∥' fst closest_in_strip -- snd closest_in_strip '∥
                      ≤ ∥' fst pre_closest_pair -- snd pre_closest_pair '∥)%dec_dist
                 then closest_in_strip
                 else pre_closest_pair
         | _, _ => pre_closest_pair
       end.
  (*Lemma right_most_left_most_correct
        (ls_left ls_right : list point.t)
        (H_left : ls_left <> []) (H_right : ls_right <> [])
        (median : point.t)
        (left_correct : List.Forall (fun pt => pt ≤ median) ls_left)
        (right_correct : List.Forall (fun pt => median ≤ pt) ls_right)
        (no_dup_median : (median ∈ ls_left /\ ¬ median ∈ ls_right) \/ (¬ median ∈ ls_right))
        (triangle :*)
  Section correct.
    Context (median : point.t)
            (pre_closest_pair : point.t * point.t)
            (strip : list point.t).

    Let post_closest_pair := get_closest_points_in_strip median pre_closest_pair strip.

    Theorem get_closest_points_in_strip_closer
    : (∥' fst post_closest_pair -- snd post_closest_pair '∥
        ≤ ∥' fst pre_closest_pair -- snd pre_closest_pair '∥)%dist.
    Proof.
    Admitted.
  End correct.
End MidStrip1D.

Module Type PointSet (point : Point).
  Axiom t : nat -> Type.
  Axiom split_marker : Type.

  Axiom split : forall n,
                  t n
                  -> split_marker * t (div2 n) * t (n - (div2 n)).
  Axiom points_sets_in_strip : forall n,
                                 t n
                                 -> point.distT
                                 -> list (point.t * { x : nat & t x }).

  Axiom get_two_points_dist : t 2 -> point.distT.
  Axiom get_three_points_min_dist : t 3 -> point.distT.
End PointSet.

Section tree.
  Variable node_data : Type.
  Variable leaf_data : Type.

  Inductive tree :=
  | Leaf : leaf_data -> tree
  | Node : tree -> node_data -> option tree -> tree.

  Fixpoint map_nodes_with_data
           (data : tree -> option tree -> node_data)
           (l : list tree)
  : list tree
    := match l with
         | nil => nil
         | x::nil => (Node x
                           (data x None)
                           None)::nil
         | x::y::rest => (Node x
                               (data x (Some y))
                               (Some y))
                           ::map_nodes_with_data data rest
       end.

  Fixpoint list_rect' {A} l (P : list A -> Type)
        (H0 : P nil)
        (H1 : forall x, P nil -> P (x::nil))
        (H2 : forall x y rest, P rest -> P (x::y::rest))
  : P l
    := match l as l return P l with
         | nil => H0
         | x::nil => H1 _ H0
         | x::y::rest => H2 x y rest (@list_rect' _ rest P H0 H1 H2)
       end.

  Lemma map_nodes_with_data_length data x y rest
  : List.length (map_nodes_with_data data (x::y::rest)) < List.length (x::y::rest).
  Proof.
    eapply (@list_rect' _ rest); simpl.
    - repeat constructor.
    - intros; repeat constructor.
    - intros. apply lt_S_n in H.
      repeat apply lt_n_S.
      etransitivity; try eassumption.
      auto.
  Defined.

  Function list_to_tree_helper data (l : list tree) {measure List.length l}
  : option tree
    := match map_nodes_with_data data l with
         | nil => None
         | x::nil => Some x
         | l' => list_to_tree_helper data l'
       end.
  Proof.
    intros.
    subst.
    destruct l as [|?[|?[|?[]]]];
    try solve [ inversion_clear teq; auto ].
    rewrite <- teq.
    apply map_nodes_with_data_length.
  Defined.

  Definition list_to_tree data (l : list leaf_data)
  : option tree
    := list_to_tree_helper data (map Leaf l).
End tree.



Module ClosestPoints (point : Point) (point_set : PointSet point).
  (** At each node of the tree, we store the left point-set, the right point-set, and a function that takes the distance and provides us with a strip of point-lists to inspect.  At each leaf, which represents at most three points, we store the minimum square distance. *)

  Local Hint Resolve div2_decr le_n_S lt_n_S le_n_S.
  Local Hint Constructors le.
  Local Hint Extern 2 => progress hnf.
  Local Hint Extern 2 => progress simpl.
  Local Hint Extern 2 => progress subst.
  Local Hint Extern 2 => unfold lt.

  Definition make_algorithm_tree_from_point_set__helper
  : ∀ x : nat,
      (∀ y : nat,
         y < x
         → point_set.t y
         → tree
             ({x0 : nat & point_set.t x0} * {x0 : nat & point_set.t x0} *
              point_set.split_marker *
              (point.distT → list (point.t * {x0 : nat & point_set.t x0})))
             point.distT + ({y = 0} + {y = 1}))
      → point_set.t x
      → tree
          ({x0 : nat & point_set.t x0} * {x0 : nat & point_set.t x0} *
           point_set.split_marker *
           (point.distT → list (point.t * {x0 : nat & point_set.t x0})))
          point.distT + ({x = 0} + {x = 1}).
  Proof.
    intros n make_algorithm_tree_from_point_set.
    refine (match n as n' return n' = n -> point_set.t n' -> _ + ({n' = 0} + {n' = 1}) with
              | 0 => fun _ _ => inr (left eq_refl)
              | 1 => fun _ _ => inr (right eq_refl)
              | 2 => fun _ s => inl (Leaf _ (point_set.get_two_points_dist s))
              | 3 => fun _ s => inl (Leaf _ (point_set.get_three_points_min_dist s))
              | n' => fun H s => let split_pts := point_set.split s in
                                 let marker := fst (fst split_pts) in
                                 let left_set := snd (fst split_pts) in
                                 let right_set := snd split_pts in
                                 let left_tree := make_algorithm_tree_from_point_set _ _ left_set in
                                 let right_tree := make_algorithm_tree_from_point_set _ _ right_set in
                                 inl (Node
                                        (match left_tree with
                                           | inl t => t
                                           | inr (left eq0) => match Nat.neq_succ_0 _ eq0 with end
                                           | inr (right eq1) => match Nat.neq_succ_0 _ (Nat.succ_inj _ _ eq1) with end
                                         end)
                                        (existT _ _ left_set,
                                         existT _ _ right_set,
                                         marker,
                                         (point_set.points_sets_in_strip s))
                                        (match right_tree with
                                           | inl t => Some t
                                           | inr _ => None
                                         end))
            end eq_refl);
    auto;
    subst.
    cbv beta iota zeta delta [div2].
    fold div2.
    repeat rewrite Nat.sub_succ.
    refine (@transitivity _ _ _ _ (S _) _ _ _).
    * unfold lt.
      apply le_n_S.
      eapply le_minus.
    * auto.
  Defined.

  Definition make_algorithm_tree_from_point_set
           (n : nat) (points : point_set.t n)
  : (tree ({ x : _ & point_set.t x } *
           { x : _ & point_set.t x } *
           point_set.split_marker *
           (point.distT -> list (point.t * { x : _ & point_set.t x })))
          point.distT)
    + ({n = 0} + {n = 1}).
  Proof.
    revert points.
    apply (Fix lt_wf) with (x := n); clear n.
    exact make_algorithm_tree_from_point_set__helper.
  Defined.

  Definition walk_algorithm_tree_in_order
             (tr : tree ({ x : _ & point_set.t x } *
                         { x : _ & point_set.t x } *
                         point_set.split_marker *
                         (point.distT -> list (point.t * { x : _ & point_set.t x })))
                        point.distT)
             (handle_node : list (point.t * { x : _ & point_set.t x }) -> point.distT)
  : list ({ x : _ & point_set.t x } *
                         { x : _ & point_set.t x } *
                         point_set.split_marker *
                         (point.distT -> list (point.t * { x : _ & point_set.t x })))
                        point.distTpoint.distT * point_set.split_marker * list (point.t * { x : _ & point_set.t x }) ).
    Print tree.
End ClosestPoints.

Module NatPoint <: Point.
  Definition t := nat.
  Definition distT := nat.
  Definition min_dist := min.
  Definition get_dist (x y : t) := ∥' x -- y '∥.
  Definition x_le : t -> t -> Prop := le.
  Definition dist_le : distT -> distT -> Prop := le.

  Definition x_le_dec := le_dec.
  Definition dist_le_dec := le_dec.
  Instance x_le_preo : PreOrder x_le := _.
  Instance dist_le_preo : PreOrder dist_le := _.
  Instance x_le_total : Total x_le := _.
  Instance dist_le_total : Total dist_le := _.
  Module Notations.
  End Notations.

  (** We take in the median point, the smallest distance we know
      about, and another point.  We say that a point is in the strip
      if its distance to the median is less than or equal to the
      smallest distance we know about. *)
  Definition point_in_strip_close_enough : t -> distT -> t -> bool
    := fun pt1 dist pt2 => if (∥' pt1 -- pt2 '∥ ≤ dist)%dec then true else false.
End NatPoint.

Module Type SplitMarker (point : Point).
  Axiom t : Type.
  Axiom make_split_marker : forall (left : list point.t)
                                   (median : option point.t)
                                   (right : list point.t),
                              t.
End SplitMarker.

Fixpoint count_occ_acc A B (P : B -> A -> B * bool) (acc : B) n (v : Vector.t A n)
: nat
  := match v with
       | Vector.nil => 0
       | Vector.cons x _ xs => let Px := P acc x in
                               (if snd Px then 1 else 0) + count_occ_acc P (fst Px) xs
     end.

Fixpoint vector_partition A B (f : B -> A -> B * bool) (acc : B) n (v : Vector.t A n)
: Vector.t A (count_occ_acc f acc v) * Vector.t A (n - count_occ_acc f acc v).
Proof.
  refine match v as v in Vector.t _ n return
               Vector.t A (count_occ_acc f acc v) * Vector.t A (n - count_occ_acc f acc v)
         with
           | Vector.nil => (Vector.nil _, Vector.nil _)
           | Vector.cons x n' xs => let fax := f acc x in
                                    let xs_part := (@vector_partition _ _ f (fst fax) _ xs) in
                                    if snd fax as fx return
                                       (Vector.t A ((if fx then 1 else 0) + count_occ_acc f (fst fax) xs) *
                                        Vector.t A (S n' - ((if fx then 1 else 0) + count_occ_acc f (fst fax) xs)))
                                    then (Vector.cons _ x _ (fst xs_part),
                                          snd xs_part)
                                    else (fst xs_part,
                                          _)
         end.
  generalize (snd xs_part); clear xs_part n v.
  change (0 + ?n) with n.
  generalize (count_occ_acc f (fst fax) xs); clear fax.
  intro n.
  clear xs.
  revert n'.
  induction n; intro n'.
  - exact (fun v' =>
             Vector.cons
               _ x _
               (match n' as n' return Vector.t A (n' - 0) -> Vector.t A n' with
                  | 0 => fun v' => v'
                  | S n'' => fun v' => v'
                end v')).
  - destruct n'.
    + exact (fun v' => v').
    + exact (IHn _).
Defined.

Definition acc_at_most (at_most : nat) A (f : A -> bool) : nat -> A -> nat * bool
  := fun count a => if lt_dec count at_most
                    then ((if f a then 1 else 0) + count, f a)
                    else (count, false).

Definition vector_partition_at_most A (f : A -> bool) (at_most : nat) n (v : Vector.t A n)
  := vector_partition (acc_at_most at_most f)
                      0
                      v.

Definition vector_transport_minus
: ∀ (A : Type) (k' : nat),
    A
    → ∀ n'' : nat,
        S k' < n'' → Vector.t A (n'' - S k') → Vector.t A (n'' - k').
Proof.
  intros A k' x.
  induction k'.
  - intros n'' H v.
    destruct n'' as [|[|n'']].
    + exact (Vector.nil _).
    + exact (Vector.cons _ x _ v).
    + exact (Vector.cons _ x _ v).
  - intros n'' H v.
    destruct n'' as [|[|n'']].
    + exact (Vector.nil _).
    + exact (Vector.nil _).
    + exact (IHk' _ (lt_S_n _ _ H) v).
Defined.

Definition vector_quick_select_helper
: ∀ (A : Type) (le : A → A → Prop),
    (∀ x y : A, {le x y} + {¬le x y})
    → ∀ x : nat,
        (∀ y : nat,
           y < x
           → ∀ k : nat,
               k < y
               → Vector.t A y → (A + {y = 0}) * Vector.t A k * Vector.t A (y - k))
        → ∀ k : nat,
            k < x
            → Vector.t A x → (A + {x = 0}) * Vector.t A k * Vector.t A (x - k).
Proof.
  intros A le le_dec.
  intros n vector_quick_select k H v.
  refine (match v as v' in Vector.t _ n', k as k' return
                n' = n -> k' < n' -> (A + {n' = 0}) * Vector.t A k' * Vector.t A (n' - k')
          with
            | Vector.nil, 0 => fun _ _ => (inright eq_refl, Vector.nil _, Vector.nil _)
            | Vector.nil, S k' => fun _ H => match lt_n_0 _ H : False with end
            | Vector.cons x n'' xs, 0 =>
              match xs as xs' in Vector.t _ n''' return
                    S n''' = n -> 0 < S n''' -> _
              with
                | Vector.nil => fun _ _ => (inleft x, Vector.nil _, Vector.cons _ x _ (Vector.nil _))
                | Vector.cons y n''' ys =>
                  fun _ _ =>
                    let rest := @vector_quick_select _ _ 0 (lt_0_Sn _) (Vector.cons _ y _ ys) in
                    let min_v := fst (fst rest) in
                    (match min_v with
                       | inright pf0 => _
                       | inleft min_v' => inleft (if le_dec x min_v' then x else min_v')
                     end,
                     Vector.nil _,
                     Vector.cons _ x _ (Vector.cons _ y _ ys))
              end
            | Vector.cons x n'' xs, S k' =>
              fun H' H =>
                let rest_k' := @vector_quick_select _ _ k' (le_S_n _ _ H) xs in
                match (fst (fst rest_k')) with
                  | inright pf1 => match lt_n_0 _ (lt_S_n _ _ (@eq_rect nat _ (fun n'' => _ < S n'') H _ pf1)) with end
                  | inleft fst_rest_k' =>
                    if le_dec x fst_rest_k'
                    (** If we are smaller than the [k']th element, then we belong on the left, and can reuse the same value for the [S k']th element *)
                    then (inleft fst_rest_k',
                          Vector.cons _ x _ (snd (fst rest_k')),
                          snd rest_k')
                    else match lt_eq_lt_dec n'' (S k') with
                           | inleft (left n''_lt_Sk') =>
                             match le_Sn_n _ (le_trans _ _ _ H n''_lt_Sk') with end
                           | inleft (right n''_eq_Sk') => (** We are larger than the [k']th element, and, in fact, the only such element (because [S k' = n'']), so we have the element we are looking for *)
                             (inleft x,
                              Vector.cons _ x _ (snd (fst rest_k')),
                              snd rest_k')
                           | inright Sk'_lt_n'' => (** We are larger than the [k']th element, so we go on the right of the [S k'] partition *)
                             let rest_Sk' := @vector_quick_select _ _ (S k') Sk'_lt_n'' xs in
                             (match fst (fst rest_Sk') with
                                | inright pf2 => _
                                | inleft fst_rest_Sk' => inleft fst_rest_Sk'
                              end,
                              snd (fst rest_Sk'),
                              vector_transport_minus x (Sk'_lt_n'') (snd rest_Sk'))
                         end
                end
          end eq_refl H);
    solve [ subst; eauto ].
Defined.

(** We get the [k]th largest element (0 means smallest), and partition the array into elements [<=] the [k]th one, andx [>=] the [k]th one.  The [k]th element sits in the second vector.  If [k > n], then the first list contains everything, and the second list is [nil]. *)
Definition vector_quick_select A (le : A -> A -> Prop)
         (le_dec : forall x y, {le x y} + {~le x y})
         k n
         (H : k < n)
         (v : Vector.t A n)
: (A + {n = 0}) * Vector.t A k * Vector.t A (n - k).
Proof.
  revert k H v.
  apply (Fix lt_wf) with (x := n); clear n.
  exact (@vector_quick_select_helper A le le_dec).
Defined.

Inductive vector_split_correct_order A : forall x y z, Vector.t A x -> Vector.t A y -> Vector.t A z -> Type :=
| split_nil : vector_split_correct_order (Vector.nil _) (Vector.nil _) (Vector.nil _)
| split_left : forall x y z v1 v2 v3,
                 @vector_split_correct_order A x y z v1 v2 v3
                 -> forall k,
                      vector_split_correct_order (Vector.cons _ k _ v1) v2 (Vector.cons _ k _ v3)
| split_right : forall x y z v1 v2 v3,
                  @vector_split_correct_order A x y z v1 v2 v3
                  -> forall k,
                       vector_split_correct_order v1 (Vector.cons _ k _ v2) (Vector.cons _ k _ v3).

Notation "[]" := (Vector.nil _) : vector_scope.
Notation "h :: t" := (Vector.cons _ h _ t) (at level 60, right associativity) : vector_scope.
Bind Scope vector_scope with Vector.t.
Delimit Scope vector_scope with vector.

Hint Constructors vector_split_correct_order.

Definition test_qselect := Eval lazy in (fun n => @vector_quick_select nat le le_dec (div2 (S n)) (S n) (lt_div2 _ (lt_0_Sn _))) _ (1::2::3::4::5::[])%vector.
Check eq_refl : test_qselect = (inleft 3, 1::2::[], 3::4::5::[])%vector.

Lemma vector_split_correct_order_refl1 A x v
: @vector_split_correct_order A _ x _ (Vector.nil _) v v.
Proof.
  induction v; eauto.
Qed.

Lemma vector_split_correct_order_refl2 A x v
: @vector_split_correct_order A x _ _ v (Vector.nil _) v.
Proof.
  induction v; eauto.
Qed.

Hint Resolve vector_split_correct_order_refl1 vector_split_correct_order_refl2.

Lemma quick_select_correct A (le : A -> A -> Prop)
      (le_dec : forall x y, {le x y} + {~le x y})
      k n
      (H : k < n)
      (v : Vector.t A n)
      (res := @vector_quick_select A le le_dec k n H v)
: vector_split_correct_order (snd (fst res)) (snd res) v.
Proof.
  unfold vector_quick_select in res.
  subst res.
  revert k H.
  induction v; eauto.
  { simpl.
    induction k; intros; simpl in *.
    { erewrite Fix_eq; destruct v; simpl in *; eauto;
      clear;
      repeat (intro || apply functional_extensionality_dep);
      unfold vector_quick_select_helper;
      destruct_in_match_if atomic; rewrite_hyp; simpl; trivial;
      destruct_in_match_if ltac:(fun _ => idtac);
      simpl; subst; trivial. }
    { erewrite Fix_eq; destruct v; simpl in *; eauto;
      try do 2 destruct_in_match_if' ltac:(fun _ => idtac);
      simpl;
      eauto;
      admit. }
  }
Qed.

Fixpoint take_while A (f : A -> bool) n (v : Vector.t A n) : { x : nat & Vector.t A x }
  := match v with
       | Vector.nil => existT _ _ (Vector.nil _)
       | Vector.cons x _ xs => if f x
                               then existT _ _ (Vector.cons _ x _ (projT2 (take_while f xs)))
                               else existT _ _ (Vector.nil _)
     end.

Module NaivePointSet (point : Point) (splitter : SplitMarker point) <: PointSet point.
  Definition t := Vector.t point.t.
  Definition split_marker := splitter.t.

  Definition split : forall n,
                       t n
                       -> split_marker * t (div2 n) * t (n - (div2 n))
    := fun n =>
         match n as n return t n -> _ * t (div2 n) * t (n - div2 n) with
           | 0 => fun _ => (splitter.make_split_marker List.nil None List.nil, Vector.nil _, Vector.nil _)
           | S n' => fun all_points =>
                       let split_pts := @vector_quick_select
                                          _
                                          point.x_le point.x_le_dec
                                          (div2 (S n'))
                                          (S n')
                                          (lt_div2 _ (lt_0_Sn _))
                                          all_points in
                       let median := fst (fst split_pts) in
                       let left_tree := snd (fst split_pts) in
                       let right_tree := snd split_pts in
                       match median with
                         | inright pf => match Nat.neq_succ_0 _ pf with end
                         | inleft median_v =>
                           (splitter.make_split_marker
                              (Vector.to_list left_tree)
                              (Some median_v)
                              (Vector.to_list right_tree),
                            left_tree,
                            right_tree)
                       end
         end.

  Fixpoint points_sets_in_strip n (pts : t n) (max_dist : point.distT) {struct pts}
  : list (point.t * { x : nat & t x })
    := match pts with
         | Vector.nil => List.nil
         | Vector.cons x _ xs =>
           (x, take_while (fun y => point.point_in_strip_close_enough x max_dist y)
                          xs)
             ::points_sets_in_strip xs max_dist
       end.


  Definition get_two_points_dist : t 2 -> point.distT.
  Proof.
    intro v.
    inversion_clear v as [|x ? v']; rename v' into v.
    inversion_clear v as [|y ? v']; rename v' into v.
    exact (point.get_dist x y).
  Defined.

  Definition get_three_points_min_dist : t 3 -> point.distT.
  Proof.
    intro v.
    inversion_clear v as [|x ? v']; rename v' into v.
    inversion_clear v as [|y ? v']; rename v' into v.
    inversion_clear v as [|z ? v']; rename v' into v.
    exact (point.min_dist (point.min_dist (point.get_dist x y) (point.get_dist y z)) (point.get_dist x z)).
  Defined.
End NaivePointSet.



Module NatPrinter.
  Local Open Scope string_scope.

  Fixpoint add_to_row (x : nat) (l : list bool) : list bool :=
    match x with
      | 0 => match l with
               | nil => true::nil
               | x::xs => true::xs
             end
      | S x' => match l with
                  | nil => false::add_to_row x' nil
                  | l0::ls => l0::add_to_row x' ls
                end
    end.

  Fixpoint list_to_row (l : list nat) (g : list bool) : list bool :=
    match l with
      | nil => g
      | pt::ls => list_to_row ls (add_to_row pt g)
    end.

  Fixpoint row_to_string (lines : nat -> string) (point_disp : nat -> string) (l : list bool) : string :=
    ((lines 0)
       ++ match l with
            | nil => EmptyString
            | b::ls => (if b then point_disp 0(*"*"(*•*)*) else " ")
                         ++ (row_to_string (fun n => lines (S n)) (fun n => point_disp (S n)) ls)
          end)%string.

  (*Fixpoint repeat {T} (n : nat) (v : T) :=
    match n with
      | 0 => nil
      | S n' => v::repeat n' v
    end.

  Definition pad_right {T} (default : T) (new_len : nat) (l : list T) : list T :=
    l ++ repeat (new_len - List.length l) default.

  Definition normalize_grid {T} (g : list (list T)) (default : T) :=
    let max_length := fold_left Arith.Max.max (map (@List.length _) g) 0 in
    map (pad_right default max_length) g.

  Definition string_list_of_grid (lines : nat -> string) (grid : list (list bool)) : list string :=
    map (row_to_string lines) (normalize_grid grid false).*)

  Definition string_list_of_nats (lines : nat -> string) (point_disp : nat -> string)
             (points : list nat) : string :=
    row_to_string lines point_disp (list_to_row points nil).

  Ltac print t := let t' := (eval compute in t) in idtac t'.
  Ltac print_list l := print (string_list_of_nats (fun _ => "") (fun _ => "*") l).
  Ltac print_list_with_lines l lines :=
    print (string_list_of_nats (fun x =>
                                  match lines with
                                    | nil => " "
                                    | x0::xs => if eq_nat_dec x0 x then "|"
                                                else if in_dec eq_nat_dec x lines then ":"(*"⋮"*)
                                                     else " "
                                  end)
                               (fun _ => "*")
                               l).
  Ltac print_list_with_lines_and_points l lines oh_points bold_points :=
    print (string_list_of_nats (fun x =>
                                  match lines with
                                    | nil => " "
                                    | x0::xs => if eq_nat_dec x0 x then "|"
                                                else if in_dec eq_nat_dec x lines then ":"(*"⋮"*)
                                                     else " "
                                  end)
                               (fun x =>
                                  if in_dec eq_nat_dec x oh_points then "o"
                                  else if in_dec eq_nat_dec x bold_points then "●"
                                       else "*")
                               l).
  Goal True.
    print_list (1::5::7::15::nil).
    print_list (1::5::7::30::nil).
    print_list_with_lines (1::5::10::18::nil) (11::nil).
    print_list_with_lines (1::5::10::18::nil) (6::11::nil).
    print_list_with_lines_and_points (1::5::10::18::nil) (6::11::nil) (1::nil) (10::nil).
  Abort.
End NatPrinter.

Module ImageSplitMarker <: SplitMarker NatPoint.
  Module point := NatPoint.
  (** An image has a list of points in the grid, and a list of line locations. *)
  Definition t := (list point.t * list point.t)%type.
  Definition make_split_marker
             (left : list point.t)
             (median : option point.t)
             (right : list point.t)
  : t
    := ((left ++ right)%list,
        match median with
          | Some pt => [pt]
          | _ => nil
        end).
End ImageSplitMarker.

Module PointSet1D := NaivePointSet NatPoint ImageSplitMarker.
Module ClosestPoints1D := ClosestPoints NatPoint PointSet1D.

Goal True.
  pose (@ClosestPoints1D.make_algorithm_tree_from_point_set
          _ (1::5::2::15::13::[])%vector).
  hnf in s.
  lazy [NatPoint.t
          NatPoint.point_in_strip_close_enough
          ImageSplitMarker.make_split_marker
          Vector.to_list
          PointSet1D.t
          NatPoint.get_dist
          NatPoint.distT
          abs_minus
          le_dec
          le_gt_dec
          le_lt_dec
          nat_rect
          nat_rec
          nat_ind
          PointSet1D.split_marker
          sumbool_rec
          sumbool_rect
          sumbool_ind
          ImageSplitMarker.t
          minus
          div2
          List.app
          NatPoint.x_le
          NatPoint.x_le_dec] in s.
  Set Printing All.

  simpl in s.
  lazy in s.

Print ClosestPoints1D.

Definition point := prod nat nat.
Bind Scope point_scope with point.
Delimit Scope point_scope with point.
Definition pt_x : point -> nat := fst.
Definition pt_y : point -> nat := snd.
Definition Build_point : nat -> nat -> point := pair.
Opaque point pt_x pt_y Build_point.
Notation "( x , y , .. , z )" := (Build_point .. (Build_point x y) .. z) : point_scope.

Local Notation "p '.(x)'" := (pt_x p) (at level 5, no associativity).
Local Notation "p '.(y)'" := (pt_y p) (at level 5, no associativity).

Local Open Scope string_scope.
Local Open Scope list_scope.

Module GridPrinter.
  Local Transparent point pt_x pt_y Build_point.

  Fixpoint add_to_row (x : nat) (l : list bool) : list bool :=
    match x with
      | 0 => match l with
               | nil => true::nil
               | x::xs => true::xs
             end
      | S x' => match l with
                  | nil => false
                  | l0::ls => l0
                end::add_to_row x' l
    end.

  Fixpoint add_to_grid (x y : nat) (g : list (list bool)) : list (list bool)
    := match y with
         | 0 => match g with
                  | nil => (add_to_row x nil)::nil
                  | r::rs => (add_to_row x r)::rs
                end
         | S y' => match g with
                     | nil => nil::add_to_grid x y' nil
                     | r::rs => r::add_to_grid x y' rs
                   end
       end.

  Fixpoint list_to_grid (l : list point) (g : list (list bool)) : list (list bool) :=
    match l with
      | nil => g
      | pt::ls => list_to_grid ls (add_to_grid pt.(x) pt.(y) g)
    end.

  Fixpoint row_to_string (lines : nat -> string) (l : list bool) : string :=
    ((lines 0)
       ++ match l with
            | nil => EmptyString
            | b::ls => (if b then "*"(*•*) else " ")
                         ++ (row_to_string (fun n => lines (S n)) ls)
          end)%string.

  Fixpoint repeat {T} (n : nat) (v : T) :=
    match n with
      | 0 => nil
      | S n' => v::repeat n' v
    end.

  Definition pad_right {T} (default : T) (new_len : nat) (l : list T) : list T :=
    l ++ repeat (new_len - List.length l) default.

  Definition normalize_grid {T} (g : list (list T)) (default : T) :=
    let max_length := fold_left Arith.Max.max (map (@List.length _) g) 0 in
    map (pad_right default max_length) g.

  Definition string_list_of_grid (lines : nat -> string) (grid : list (list bool)) : list string :=
    map (row_to_string lines) (normalize_grid grid false).

  Definition string_list_of_coords (lines : nat -> string) (points : list point) : list string :=
    string_list_of_grid lines (list_to_grid points nil).

  Ltac print_grid grid :=
    match eval compute in grid with
      | nil => idtac ""
      | ?r::?rs => idtac r; print_grid rs
    end.

  Ltac print_list l := print_grid (string_list_of_coords (fun _ => "") l).
  Ltac print_list_with_lines l lines :=
    print_grid (string_list_of_coords (fun x =>
                                         match lines with
                                           | nil => " "
                                           | x0::xs => if eq_nat_dec x0 x then "|"
                                                       else if in_dec eq_nat_dec x lines then ":"(*"⋮"*)
                                                            else " "
                                         end)
                                      l).
  Goal True.
    print_list ((1,1)::(2,3)::(4,5)::nil).
    print_list_with_lines ((1,1)::(2,3)::(4,5)::nil) (3::nil).
    print_list_with_lines ((1,1)::(2,3)::(4,5)::nil) (2::3::nil).
  Abort.
End GridPrinter.



Section distance.
  Definition abs_minus (x y : nat) :=
    if le_dec x y then y - x else x - y.
  Local Infix "-" := abs_minus.

  Definition square_distance (x1 y1 x2 y2 : nat) := (x1 - x2)^2 + (y1 - y2)^2.
End distance.

Definition point_square_distance (p1 p2 : point) := square_distance p1.(x) p1.(y) p2.(x) p2.(y).

Notation "∥ p1 -- p2 ∥²" := (point_square_distance p1 p2) : nat_scope.

Local Infix "<" := lt_dec : bool_scope.
Local Infix "<=" := le_dec : bool_scope.
Local Infix ">" := gt_dec : bool_scope.
Local Infix ">=" := ge_dec : bool_scope.

Definition option_min : option nat -> option nat -> option nat
  := fun a b => match a, b with
                  | None, _ => b
                  | _, None => a
                  | Some a, Some b => Some (min a b)
                end.

(** We implement the brute force algorithm as a sanity check *)
Fixpoint n2_brute_force (pts : list point) : option nat
  := match pts with
       | nil => None
       | pt::pts' => fold_left option_min
                               (map (fun pt' => Some ∥ pt' -- pt ∥²)
                                    pts')
                               (n2_brute_force pts')
     end.

Module Type Point.
  Axiom t : Type.
  Axiom distT : Type.
  Axiom min_dist : distT -> distT -> distT.
  Axiom get_dist : t -> t -> distT.
  Axiom x_le : t -> t -> Prop.
  Axiom y_le : t -> t -> Prop.
  Axiom x_le_dec : forall x y, {x_le x y} + {~x_le x y}.
  Axiom y_le_dec : forall x y, {y_le x y} + {~y_le x y}.
  Axiom point_in_strip_close_enough : t -> distT -> t -> bool.
End Point.

Module Type PointSet (point : Point).
  Axiom t : nat -> Type.
  Axiom split_marker : Type.

  Axiom split : forall n,
                  t n
                  -> split_marker * t (div2 n) * t (n - (div2 n)).
  Axiom points_sets_in_strip : forall n,
                                 t n
                                 -> point.distT
                                 -> list (point.t * { x : nat & t x }).

  Axiom get_two_points_dist : t 2 -> point.distT.
  Axiom get_three_points_min_dist : t 3 -> point.distT.
End PointSet.

Section tree.
  Variable node_data : Type.
  Variable leaf_data : Type.

  Inductive tree :=
  | Leaf : leaf_data -> tree
  | Node : tree -> node_data -> option tree -> tree.

  Fixpoint map_nodes_with_data
           (data : tree -> option tree -> node_data)
           (l : list tree)
  : list tree
    := match l with
         | nil => nil
         | x::nil => (Node x
                           (data x None)
                           None)::nil
         | x::y::rest => (Node x
                               (data x (Some y))
                               (Some y))
                           ::map_nodes_with_data data rest
       end.

  Fixpoint list_rect' {A} l (P : list A -> Type)
        (H0 : P nil)
        (H1 : forall x, P nil -> P (x::nil))
        (H2 : forall x y rest, P rest -> P (x::y::rest))
  : P l
    := match l as l return P l with
         | nil => H0
         | x::nil => H1 _ H0
         | x::y::rest => H2 x y rest (@list_rect' _ rest P H0 H1 H2)
       end.

  Lemma map_nodes_with_data_length data x y rest
  : List.length (map_nodes_with_data data (x::y::rest)) < List.length (x::y::rest).
  Proof.
    eapply (@list_rect' _ rest); simpl.
    - repeat constructor.
    - intros; repeat constructor.
    - intros. apply lt_S_n in H.
      repeat apply lt_n_S.
      etransitivity; try eassumption.
      auto.
  Defined.

  Function list_to_tree_helper data (l : list tree) {measure List.length l}
  : option tree
    := match map_nodes_with_data data l with
         | nil => None
         | x::nil => Some x
         | l' => list_to_tree_helper data l'
       end.
  Proof.
    intros.
    subst.
    destruct l as [|?[|?[|?[]]]];
    try solve [ inversion_clear teq; auto ].
    rewrite <- teq.
    apply map_nodes_with_data_length.
  Defined.

  Definition list_to_tree data (l : list leaf_data)
  : option tree
    := list_to_tree_helper data (map Leaf l).
End tree.



Module ClosestPoints (point : Point) (point_set : PointSet point).
  (** At each node of the tree, we store the left point-set, the right point-set, and a function that takes the distance and provides us with a strip of point-lists to inspect.  At each leaf, which represents at most three points, we store the minimum square distance. *)

  Hint Resolve div2_decr le_n_S lt_n_S le_n_S.
  Hint Constructors le.
  Hint Extern 2 => progress hnf.
  Hint Extern 2 => progress simpl.
  Hint Extern 2 => progress subst.
  Hint Extern 2 => unfold lt.

  Definition make_algorithm_tree_from_point_set
           (n : nat) (points : point_set.t n)
  : (tree ({ x : _ & point_set.t x } *
           { x : _ & point_set.t x } *
           point_set.split_marker *
           (point.distT -> list (point.t * { x : _ & point_set.t x })))
          point.distT)
    + ({n = 0} + {n = 1}).
  Proof.
    revert points.
    apply (Fix lt_wf) with (x := n); clear n.
    intros n make_algorithm_tree_from_point_set.
    refine (match n as n' return n' = n -> point_set.t n' -> _ + ({n' = 0} + {n' = 1}) with
              | 0 => fun _ _ => inr (left eq_refl)
              | 1 => fun _ _ => inr (right eq_refl)
              | 2 => fun _ s => inl (Leaf _ (point_set.get_two_points_dist s))
              | 3 => fun _ s => inl (Leaf _ (point_set.get_three_points_min_dist s))
              | n' => fun H s => let split_pts := point_set.split s in
                                 let marker := fst (fst split_pts) in
                                 let left_set := snd (fst split_pts) in
                                 let right_set := snd split_pts in
                                 let left_tree := make_algorithm_tree_from_point_set _ _ left_set in
                                 let right_tree := make_algorithm_tree_from_point_set _ _ right_set in
                                 inl (Node
                                        (match left_tree with
                                           | inl t => t
                                           | inr (left eq0) => match Nat.neq_succ_0 _ eq0 with end
                                           | inr (right eq1) => match Nat.neq_succ_0 _ (Nat.succ_inj _ _ eq1) with end
                                         end)
                                        (existT _ _ left_set,
                                         existT _ _ right_set,
                                         marker,
                                         (point_set.points_sets_in_strip s))
                                        (match right_tree with
                                           | inl t => Some t
                                           | inr _ => None
                                         end))
            end eq_refl);
      auto;
      subst.
    cbv beta iota zeta delta [div2].
    fold div2.
    repeat rewrite Nat.sub_succ.
    refine (@transitivity _ _ _ _ (S _) _ _ _).
    * unfold lt.
      apply le_n_S.
      eapply le_minus.
    * auto.
  Defined.
End ClosestPoints.

Module NatPoint : Point.
  Definition t := point.
  Definition distT := nat.
  Definition min_dist := min.
  Definition get_dist (x y : point) := ∥ x -- y ∥².
  Definition x_le p1 p2 := le p1.(x) p2.(x).
  Definition y_le p1 p2 := le p1.(y) p2.(y).
  Definition x_le_dec : forall x y, {x_le x y} + {~x_le x y}
    := fun _ _ => le_dec _ _.
  Definition y_le_dec : forall x y, {y_le x y} + {~y_le x y}
    := fun _ _ => le_dec _ _.
  Definition point_in_strip_close_enough (pt1 : t) (max_square_distance : distT) (pt2 : t) : bool
    := if ((Nat.max (pt1.(y) - pt2.(y)) (pt2.(y) - pt1.(y))) ^ 2 <= 2 * max_square_distance)%bool
       then true
       else false.
End NatPoint.

Module Type SplitMarker (point : Point).
  Axiom t : Type.
  Axiom make_split_marker : forall (left : list point.t)
                                   (median : option point.t)
                                   (right : list point.t),
                              t.
End SplitMarker.

Fixpoint count_occ_acc A B (P : B -> A -> B * bool) (acc : B) n (v : Vector.t A n)
: nat
  := match v with
       | Vector.nil => 0
       | Vector.cons x _ xs => let Px := P acc x in
                               (if snd Px then 1 else 0) + count_occ_acc P (fst Px) xs
     end.

Fixpoint vector_partition A B (f : B -> A -> B * bool) (acc : B) n (v : Vector.t A n)
: Vector.t A (count_occ_acc f acc v) * Vector.t A (n - count_occ_acc f acc v).
Proof.
  refine match v as v in Vector.t _ n return
               Vector.t A (count_occ_acc f acc v) * Vector.t A (n - count_occ_acc f acc v)
         with
           | Vector.nil => (Vector.nil _, Vector.nil _)
           | Vector.cons x n' xs => let fax := f acc x in
                                    let xs_part := (@vector_partition _ _ f (fst fax) _ xs) in
                                    if snd fax as fx return
                                       (Vector.t A ((if fx then 1 else 0) + count_occ_acc f (fst fax) xs) *
                                        Vector.t A (S n' - ((if fx then 1 else 0) + count_occ_acc f (fst fax) xs)))
                                    then (Vector.cons _ x _ (fst xs_part),
                                          snd xs_part)
                                    else (fst xs_part,
                                          _)
         end.
  generalize (snd xs_part); clear xs_part n v.
  change (0 + ?n) with n.
  generalize (count_occ_acc f (fst fax) xs); clear fax.
  intro n.
  clear xs.
  revert n'.
  induction n; intro n'.
  - exact (fun v' =>
             Vector.cons
               _ x _
               (match n' as n' return Vector.t A (n' - 0) -> Vector.t A n' with
                  | 0 => fun v' => v'
                  | S n'' => fun v' => v'
                end v')).
  - destruct n'.
    + exact (fun v' => v').
    + exact (IHn _).
Defined.

Definition acc_at_most (at_most : nat) A (f : A -> bool) : nat -> A -> nat * bool
  := fun count a => if lt_dec count at_most
                    then ((if f a then 1 else 0) + count, f a)
                    else (count, false).

Definition vector_partition_at_most A (f : A -> bool) (at_most : nat) n (v : Vector.t A n)
  := vector_partition (acc_at_most at_most f)
                      0
                      v.

(** We get the [k]th largest element (0 means smallest), and partition the array into elements [<=] the [k]th one, andx [>=] the [k]th one.  The [k]th element sits in the second vector.  If [k > n], then the first list contains everything, and the second list is [nil]. *)
Definition vector_quick_select A (le : A -> A -> Prop)
         (le_dec : forall x y, {le x y} + {~le x y})
         k n
         (H : k < n)
         (v : Vector.t A n)
: (A + {n = 0}) * Vector.t A k * Vector.t A (n - k).
Proof.
  revert k H v.
  apply (Fix lt_wf) with (x := n); clear n.
  intros n vector_quick_select k H v.
  refine (match v as v' in Vector.t _ n', k as k' return
                n' = n -> k' < n' -> (A + {n' = 0}) * Vector.t A k' * Vector.t A (n' - k')
          with
            | Vector.nil, 0 => fun _ _ => (inright eq_refl, Vector.nil _, Vector.nil _)
            | Vector.nil, S k' => fun _ H => match lt_n_0 _ H : False with end
            | Vector.cons x n'' xs, 0 =>
              match xs as xs' in Vector.t _ n''' return
                    S n''' = n -> 0 < S n''' -> _
              with
                | Vector.nil => fun _ _ => (inleft x, Vector.nil _, Vector.cons _ x _ (Vector.nil _))
                | Vector.cons y n''' ys =>
                  fun _ _ =>
                    let rest := @vector_quick_select _ _ 0 (lt_0_Sn _) (Vector.cons _ y _ ys) in
                    let min_v := fst (fst rest) in
                    (match min_v with
                       | inright pf0 => _
                       | inleft min_v' => inleft (if le_dec x min_v' then x else min_v')
                     end,
                     Vector.nil _,
                     Vector.cons _ x _ (Vector.cons _ y _ ys))
              end
            | Vector.cons x n'' xs, S k' =>
              fun H' H =>
                let rest_k' := @vector_quick_select _ _ k' (le_S_n _ _ H) xs in
                match (fst (fst rest_k')) with
                  | inright pf1 => match lt_n_0 _ (lt_S_n _ _ (@eq_rect nat _ (fun n'' => _ < S n'') H _ pf1)) with end
                  | inleft fst_rest_k' =>
                    if le_dec x fst_rest_k'
                    (** If we are smaller than the [k']th element, then we belong on the left, and can reuse the same value for the [S k']th element *)
                    then (inleft fst_rest_k',
                          Vector.cons _ x _ (snd (fst rest_k')),
                          snd rest_k')
                    else match lt_eq_lt_dec n'' (S k') with
                           | inleft (left n''_lt_Sk') =>
                             match le_Sn_n _ (le_trans _ _ _ H n''_lt_Sk') with end
                           | inleft (right n''_eq_Sk') => (** We are larger than the [k']th element, and, in fact, the only such element (because [S k' = n'']), so we have the element we are looking for *)
                             (inleft x,
                              Vector.cons _ x _ (snd (fst rest_k')),
                              snd rest_k')
                           | inright Sk'_lt_n'' => (** We are larger than the [k']th element, so we go on the right of the [S k'] partition *)
                             let rest_Sk' := @vector_quick_select _ _ (S k') Sk'_lt_n'' xs in
                             (match fst (fst rest_Sk') with
                                | inright pf2 => _
                                | inleft fst_rest_Sk' => inleft fst_rest_Sk'
                              end,
                              snd (fst rest_Sk'),
                              _ x (Sk'_lt_n'') (snd rest_Sk'))
                         end
                end
          end eq_refl H);
    try solve [ subst; eauto ].
  clear.
  intros x H v; simpl; revert n'' H v.
  induction k'.
  - intros n'' H v.
    destruct n'' as [|[|n'']].
    + exact (Vector.nil _).
    + exact (Vector.cons _ x _ v).
    + exact (Vector.cons _ x _ v).
  - intros n'' H v.
    destruct n'' as [|[|n'']].
    + exact (Vector.nil _).
    + exact (Vector.nil _).
    + exact (IHk' _ (lt_S_n _ _ H) v).
Defined.

Inductive vector_split_correct A : forall x y z, Vector.t A x -> Vector.t A y -> Vector.t A z -> Type :=
| split_nil : vector_split_correct (Vector.nil _) (Vector.nil _) (Vector.nil _)
| split_left : forall x y z v1 v2 v3,
                 @vector_split_correct A x y z v1 v2 v3
                 -> forall k,
                      vector_split_correct (Vector.cons _ k _ v1) v2 (Vector.cons _ k _ v3)
| split_right : forall x y z v1 v2 v3,
                  @vector_split_correct A x y z v1 v2 v3
                  -> forall k,
                       vector_split_correct v1 (Vector.cons _ k _ v2) (Vector.cons _ k _ v3).

Notation "[]" := (Vector.nil _) : vector_scope.
Notation "h :: t" := (Vector.cons _ h _ t) (at level 60, right associativity) : vector_scope.
Bind Scope vector_scope with Vector.t.
Delimit Scope vector_scope with vector.

Definition test_qselect := Eval lazy in (fun n => @vector_quick_select nat le le_dec (div2 (S n)) (S n) (lt_div2 _ (lt_0_Sn _))) _ (1::2::3::4::5::[])%vector.
Check eq_refl : test_qselect = (inleft 3, 1::2::[], 3::4::5::[])%vector.

Lemma quick_select_correct A (le : A -> A -> Prop)
      (le_dec : forall x y, {le x y} + {~le x y})
      k n
      (H : k < n)
      (v : Vector.t A n)
      (res := @vector_quick_select A le le_dec k n H v)
: vector_split_correct (snd (fst res)) (snd res) v.
Proof.
  unfold vector_quick_select in res.
  subst res.
  erewrite Fix_eq.
  revert k H.


Fixpoint take_while A (f : A -> bool) n (v : Vector.t A n) : { x : nat & Vector.t A x }
  := match v with
       | Vector.nil => existT _ _ (Vector.nil _)
       | Vector.cons x _ xs => if f x
                               then existT _ _ (Vector.cons _ x _ (projT2 (take_while f xs)))
                               else existT _ _ (Vector.nil _)
     end.

Module NaivePointSet (point : Point) (splitter : SplitMarker point) <: PointSet point.
  Definition t := Vector.t point.t.
  Definition split_marker := splitter.t.

  Definition split : forall n,
                       t n
                       -> split_marker * t (div2 n) * t (n - (div2 n))
    := fun n =>
         match n as n return t n -> _ * t (div2 n) * t (n - div2 n) with
           | 0 => fun _ => (splitter.make_split_marker List.nil None List.nil, Vector.nil _, Vector.nil _)
           | S n' => fun all_points =>
                       let split_pts := @vector_quick_select
                                          _
                                          point.x_le point.x_le_dec
                                          (div2 (S n'))
                                          (S n')
                                          (lt_div2 _ (lt_0_Sn _))
                                          all_points in
                       let median := fst (fst split_pts) in
                       let left_tree := snd (fst split_pts) in
                       let right_tree := snd split_pts in
                       match median with
                         | inright pf => match Nat.neq_succ_0 _ pf with end
                         | inleft median_v =>
                           (splitter.make_split_marker
                              (Vector.to_list left_tree)
                              (Some median_v)
                              (Vector.to_list right_tree),
                            left_tree,
                            right_tree)
                       end
         end.

  Fixpoint points_sets_in_strip n (pts : t n) (max_dist : point.distT) {struct pts}
  : list (point.t * { x : nat & t x })
    := match pts with
         | Vector.nil => List.nil
         | Vector.cons x _ xs =>
           (x, take_while (fun y => point.point_in_strip_close_enough x max_dist y)
                          xs)
             ::points_sets_in_strip xs max_dist
       end.


  Definition get_two_points_dist : t 2 -> point.distT.
  Proof.
    intro v.
    inversion_clear v as [|x ? v']; rename v' into v.
    inversion_clear v as [|y ? v']; rename v' into v.
    exact (point.get_dist x y).
  Defined.

  Definition get_three_points_min_dist : t 3 -> point.distT.
  Proof.
    intro v.
    inversion_clear v as [|x ? v']; rename v' into v.
    inversion_clear v as [|y ? v']; rename v' into v.
    inversion_clear v as [|z ? v']; rename v' into v.
    exact (point.min_dist (point.min_dist (point.get_dist x y) (point.get_dist y z)) (point.get_dist x z)).
  Defined.
End NaivePointSet.

Module ImageSplitMarker (point : Point)

Print tree.
Inductive algorithm_tree (metadata : Type) (

Definition make_splits

(** Is the point in the strip about a given median?  We use an informative type so that we don't care about the implementation. *)
Definition point_in_strip (median_below median_above : nat)
           (median_correct : {median_below = median_above} + {S median_below = median_above})
           (dist : nat)
           (pt : point)
           (x := pt.(x))
           (y := pt.(y))
: {if (x < median_above)%bool then median_above - x <= dist else x - median_below <= dist}
  + {if (x < median_above)%bool then median_above - x > dist else x - median_below > dist}.
Proof.
  destruct (x < median_above)%bool;
  destruct median_correct; subst;
  apply le_gt_dec.
Defined.

Definition

(** Given a list of points, a new point, and a distance, add the new point to the list, and remove any points whose y-coordinate is further from the given point than the distance. *)
Definition update_holding_points (holding_points : list point) (new_point : point) (distance : nat) : list point
  := new_point::(filter (fun pt => if (max (pt.(y) - new_point.(y)) (new_point.(y) - pt.(y)) <= distance)%bool
                                   then true
                                   else false)
                        holding_points).

Check (eq_refl : (update_holding_points ((1,2)::(3,4)::(5,6)::nil) (7,8) 6)
                 = (7, 8) :: (1, 2) :: (3, 4) :: (5, 6) :: nil).

(** f takes in the accumulator, the current point, and a list of holding points *)
(** Note: the list of holding points should probably be backed with a doubly-linked list.  But there will be at most a constant number of points in it, so we don't actually care. *)
Definition cmp_y : relation point := (fun pt1 pt2 => pt1.(y) <= pt2.(y)).
Fixpoint fold_points_in_strip {T} (acc : T) (f : point -> list point -> T -> T)
        (strip : list point)
        (strip_sorted : Sorted cmp_y strip)
        (median_below median_above : nat)
        (median_correct : {median_below = median_above} + {S median_below = median_above})
        (dist : nat)
        (holding_points : list point)
: T.
Proof.
  refine (match strip as strip return Sorted cmp_y strip -> T with
            | nil => fun _ => acc
            | pt::pts =>
              fun is_sorted =>
                let pts_is_sorted := match is_sorted return Sorted cmp_y pts with
                                       | _ => _
                                     end in
                if point_in_strip median_correct dist pt
                then let new_acc := f pt holding_points acc in
                     let new_holding_points := update_holding_points holding_points pt dist in
                     @fold_points_in_strip _ new_acc f pts pts_is_sorted _ _ median_correct dist new_holding_points
                else fold_points_in_strip _ acc f pts pts_is_sorted _ _ median_correct dist holding_points
          end strip_sorted).
  revert is_sorted; clear; intro; abstract (inversion_clear is_sorted; assumption).
Defined.

(** Now we find the minimum distance between points in a strip *)
Definition find_min_square_dist_in_strip
           (median_below median_above : nat)
           (median_correct : {median_below = median_above} + {S median_below = median_above})
           (strip : list point) (strip_sorted : Sorted cmp_y strip)
           (half_width : nat)
: option nat
  := fold_points_in_strip
       None
       (fun pt pts cur_min => option_min
                                (fold_left option_min
                                           (map (fun pt' => Some ∥ pt' -- pt ∥²) pts)
                                           None)
                                cur_min)
       strip_sorted
       median_correct
       half_width
       nil.

Goal True.
  pose (fun H => @find_min_square_dist_in_strip 2 3 (right eq_refl) ((1,2)::(3,4)::(5,6)::(7,8)::(9,10)::(11,12)::nil) H 2).
  cbv beta delta [find_min_square_dist_in_strip] in o.
  cbv beta delta [fold_points_in_strip] in o.



Goal True.
  print_list ((1,1)::(2,3)::(4,5)::nil).
  print_list_with_lines ((1,1)::(2,3)::(4,5)::nil) (3::nil).
  print_list_with_lines ((1,1)::(2,3)::(4,5)::nil) (1::3::nil).

  print_grid (.
  match eval hnf in grid with
    | nil => idtac "a"
    | ?r::?rs => idtac r; idtac "a"; print_grid rs
  end.

Section alg.
  Variable points : list (nat * nat).

  Notation
<



Require Import Omega Arith Max.

Record point := pt { x : nat; y : nat }.


Definition abs_diff (a b : nat) := max (a - b) (b - a).

Definition sq a : nat := a * a.

Definition sqdist (a b : point) : nat
  := sq (abs_diff a.(x) b.(x)) + sq (abs_diff a.(y) b.(y)).

Lemma triangle_ineq (a b c : point)
: sqdist a c <= sqdist a b + sqdist b c.
Proof.
  unfold sqdist, abs_diff, sq.
  destruct a, b, c; simpl in *.
  SearchAbout max.
  repeat match goal with
           | [ |- context[max ?a ?b] ]
             => let H := fresh "H" in
                destruct (max_spec a b) as [[? H]|[? H]];
                  rewrite !H; clear H
         end.
  rewrite !mult_minus_distr_r, !mult_minus_distr_l.

  SearchAbout minus.
