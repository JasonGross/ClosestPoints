Require Export Vector NPeano Div2 NArith Wf Wf_nat Program.
Require Import Program.Equality.
Require Export CommonDefinitions ClosestPoints.Tactics.

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

(*Definition opaque_id_with_data {T} {T'} (x : T) (y : T') := x.
Opaque opaque_id_with_data.*)

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
                       | inright pf0 => inleft x
                       | inleft min_v' => inleft (if le_dec x min_v' then x else min_v')
                     end,
                     match snd (fst rest) in Vector.t _ n return n = 0 -> Vector.t _ n with
                       | Vector.nil => fun _ => Vector.nil _
                       | Vector.cons _ _ _ => fun H => match Nat.neq_succ_0 _ H : False with end
                     end eq_refl,
                     Vector.cons _ x _ (snd rest))
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
                                | inright pf2 => inleft fst_rest_k' (** XXX is this right? *)
                                | inleft fst_rest_Sk' => inleft fst_rest_Sk'
                              end,
                              snd (fst rest_Sk'),
                              vector_transport_minus x (Sk'_lt_n'') (snd rest_Sk'))
                         end
                end
          end eq_refl H);
    clear vector_quick_select;
    try solve [
          repeat match goal with
                   | [ H : _ = ?n |- appcontext[?n] ] => revert H
                 end;
          clear; intros;
          abstract (subst; eauto)
        ].
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

Eval lazy in (fun n => @vector_quick_select nat le le_dec (div2 (S n)) (S n) (lt_div2 _ (lt_0_Sn _))) _ (1::5::2::15::13::[])%vector.

Definition test_qselect := Eval lazy in (fun n => @vector_quick_select nat le le_dec (div2 (S n)) (S n) (lt_div2 _ (lt_0_Sn _))) _ (1::2::3::4::5::[])%vector.
Check eq_refl : test_qselect = (inleft 3, 1::2::[], 3::4::5::[])%vector.



Hint Constructors vector_split_correct_order Vector.Forall and.

Local Hint Extern 0 => progress subst_body.

Ltac revert_body_then tac :=
  match goal with
    | [ H := _ |- _ ] => revert H;
                        revert_body_then tac;
                        intro
    | _ => tac
  end.

Ltac subst_lt_1 :=
  match goal with
    | [ H : _ < 1 |- _ ] => let H' := fresh in
                            pose proof (proj1 (Nat.lt_1_r _) H) as H'
  end;
  revert_body_then ltac:(subst).

Add Parametric Morphism A n v : (fun P => @Vector.Forall A P n v)
  with signature (pointwise_relation _ impl) ==> impl
    as Vector_Forall_impl.
Proof.
  induction v; lazy in *; eauto.
  intros x y H H'.
  inversion H'; simpl_existT; subst; constructor; eauto.
Qed.

Lemma vector_quick_select_helper_correct_median
      A (le : A -> A -> Prop)
      (le_dec : forall x y, {le x y} + {~le x y})
      `{Hr : PreOrder _ le}
      `{Ht : Total _ le}
      `{Hd : forall x y, Decidable (le x y)}
      (x : nat)
      (f : ∀ y : nat,
             y < x
             → ∀ k : nat, k < y → t A y → (A + {y = 0}) * t A k * t A (y - k))
      (IH : forall y H' k H'' v
                   (res := f y H' k H'' v)
                   (lefts := snd (fst res))
                   (rights := snd res),
              match fst (fst res) with
                | inleft median =>
                  Vector.Forall (λ x0 : A, le x0 median) lefts
                  ∧ Vector.Forall (λ x0 : A, le median x0) rights
                | inright _ => y = 0
              end)
      (v : t A x) (k : nat) (H : k < x)
      (res := vector_quick_select_helper le le_dec f H v)
      (lefts := snd (fst res))
      (rights := snd res)
: match fst (fst res) with
    | inleft median =>
      Vector.Forall (λ x0 : A, le x0 median) lefts
      ∧ Vector.Forall (λ x0 : A, le median x0) rights
    | inright _ => x = 0
  end.
Proof.
  destruct v; simpl in *;
  try solve [ inversion H ].
  { destruct v; simpl in *; eauto.
    subst_lt_1.
    try solve [ simpl in *; eauto ].
    subst_body.
    destruct k; simpl in *;
    match goal with
      | [ |- appcontext[match fst (fst (f ?y ?H' ?k ?H'' ?v)) with _ => _ end] ]
        => specialize (IH y H' k H'' v);
          generalize dependent (f y H' k H'' v)
    end;
    intros [ [ [?|?] ?] ? ];
    simpl in *;
    intros;
    try match goal with
          | [ |- appcontext[if ?E then _ else _] ] => destruct E
        end;
    destruct_head and;
    try split;
    try match goal with
          | [ v : Vector.t _ 0 |- _ ]
            => generalize dependent v;
              refine (@Vector.case0 _ _ _)
        end;
    eauto;
    intros.
    { constructor; eauto.
      eapply Vector_Forall_impl; try eassumption; [ ]; lazy; eauto.
      intros; etransitivity; eauto. }
    { destruct (lt_eq_lt_dec n k) as [ [ ? | ? ] | ? ];
      eauto.
      (** WTF?  Why doesn't eauto pick this up? *)
      clear.
      reverse.
      Goal ∀ (A : Type) (le : A → A → Prop) (n k : nat) (H : S k < S (S n))
   (l : n < k),
   match
     fst
       (fst
          match
            le_Sn_n (S k)
              (le_trans (S (S k)) (S (S n)) (S k) H (le_n_S (S n) k l))
            return
              ((A + {S (S n) = 0}) * t A (S k) *
               t A match k with
                   | 0 => S n
                   | S l0 => n - l0
                   end)
          with
          end)
   with
   | inleft median =>
       Vector.Forall (λ x0 : A, le x0 median)
         (snd
            (fst
               match
                 le_Sn_n (S k)
                   (le_trans (S (S k)) (S (S n)) (S k) H (le_n_S (S n) k l))
                 return
                   ((A + {S (S n) = 0}) * t A (S k) *
                    t A match k with
                        | 0 => S n
                        | S l0 => n - l0
                        end)
               with
               end))
       ∧ Vector.Forall (λ x0 : A, le median x0)
           (snd
              match
                le_Sn_n (S k)
                  (le_trans (S (S k)) (S (S n)) (S k) H (le_n_S (S n) k l))
                return
                  ((A + {S (S n) = 0}) * t A (S k) *
                   t A match k with
                       | 0 => S n
                       | S l0 => n - l0
                       end)
              with
              end)
   | inright _ => S (S n) = 0
   end.
      Hint Extern 0 => match goal with |- appcontext[match ?E with end] => case E end.
      intros.
      match goal with |- appcontext[match ?E with end] => case E end.
      Undo.
      solve [ eauto ].
eauto.
solve [ t ].
eauto with foo.
solve [ match goal with |- appcontext[match ?E with end] => case E end ].
      match goal with
      {  apply total_decidable_neg_flip in .
SearchAbout Total.
      {


    let H := match goal with H : le ?h ?a |- appcontext[le _ ?h] => constr:(H) end in
    pose proof (fun x p => @transitivity _ le _ x _ _ p H).
    split.
    eapply Vector_Forall_impl; try eassumption; lazy. auto.
    simpl in *.
    unfold impl in *.
    simpl in *.
    eapply i.
    setoid_rewrite H2.


    SearchAbout Vector.Forall.
    split; eauto.

    specialize (IH (S n)
    subst_body; eauto.
    split.
    eauto.
    eauto.
    constructor.

    constructor.
  unfold vector_quick_select_helper in res.

Lemma vector_split_correct_median
      A (le : A -> A -> Prop)
      (le_dec : forall x y, {le x y} + {~le x y})
      k n
      (H : k < n)
      (v : Vector.t A n)
      (res := @vector_quick_select A le le_dec k _ H v)
      (lefts := snd (fst res))
      (rights := snd res)
: match fst (fst res) with
    | inleft median
      => Vector.Forall (fun x => le x median) lefts
         /\ Vector.Forall (fun x => le median x) rights
    | inright _ => n = 0
  end.
Proof.
  revert v k H res lefts rights.
  apply (Fix lt_wf) with (x := n); clear n.
  induction n.
  { intros v k H.
    inversion H. }
  { unfold vector_quick_select.

    let n := match type of v with | t ?A ?n => constr:(n) end in
    set (n' := n) in v;
      change n with n';
      assert (n' = n) by reflexivity
      generalize dependent n'.

  unfold vector_quick_select in res.
  subst_body.
  erewrite Fix_eq.

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
