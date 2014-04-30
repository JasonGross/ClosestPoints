Require Export Tactics.

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

Delimit Scope dec_scope with dec.
Infix "<=" := le_lt_dec : dec_scope.
Infix "≤" := le_lt_dec : dec_scope.
Infix "=" := eq_nat_dec : dec_scope.

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

Fixpoint take_while A (f : A -> bool) n (v : Vector.t A n) : { x : nat & Vector.t A x }
  := match v with
       | Vector.nil => existT _ _ (Vector.nil _)
       | Vector.cons x _ xs => if f x
                               then existT _ _ (Vector.cons _ x _ (projT2 (take_while f xs)))
                               else existT _ _ (Vector.nil _)
     end.

Infix "<" := lt_dec : dec_scope.
Infix "<=" := le_dec : dec_scope.
Infix ">" := gt_dec : dec_scope.
Infix ">=" := ge_dec : dec_scope.

Definition option_min : option nat -> option nat -> option nat
  := fun a b => match a, b with
                  | None, _ => b
                  | _, None => a
                  | Some a, Some b => Some (min a b)
                end.

Notation "[]" := List.nil : list_scope.

Notation "[]" := (Vector.nil _) : vector_scope.
Notation "h :: t" := (Vector.cons _ h _ t) (at level 60, right associativity) : vector_scope.
Bind Scope vector_scope with Vector.t.
Delimit Scope vector_scope with vector.

(** Given a decidable [≤] on [B] and a function [f : A → B], we can
    take the smaller [A] as decided by [f]. *)
Definition min_by {A B P} `{p : forall x y : B, Decidable (P x y)}
           (f : A -> B)
: A -> A -> A
  := fun a b => if p (f a) (f b) then a else b.
