Require Export Ascii String List Arith.

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

  Definition string_list_of_nats_with_lines l lines :=
    (string_list_of_nats (fun x =>
                            match lines with
                              | nil => " "
                              | x0::xs => if eq_nat_dec x0 x then "|"
                                          else if in_dec eq_nat_dec x lines then ":"(*"⋮"*)
                                               else " "
                            end)
                         (fun _ => "*")
                         l).

  Fixpoint find_symbol_of_point pt symb_points :=
    match symb_points with
      | nil => "*"
      | (symb, pts)::symb_points'
        => if in_dec eq_nat_dec pt pts
           then symb
           else find_symbol_of_point pt symb_points'
    end.

  Definition string_list_of_nats_with_lines_and_points l lines symb_points :=
    string_list_of_nats (fun x =>
                           match lines with
                             | nil => " "
                             | x0::xs => if eq_nat_dec x0 x then "|"
                                         else if in_dec eq_nat_dec x lines then ":"(*"⋮"*)
                                              else " "
                           end)
                        (fun x =>
                           find_symbol_of_point x symb_points(*
                           if in_dec eq_nat_dec x oh_points then "o"
                           else if in_dec eq_nat_dec x bold_points then "●"
                                else "*"*))
                        l.

  Ltac print t := let t' := (eval lazy in t) in idtac t'.
  Ltac print_list l := print (string_list_of_nats (fun _ => "") (fun _ => "*") l).
  Ltac print_list_with_lines l lines :=
    print (string_list_of_nats_with_lines l lines).
  Ltac print_list_with_lines_and_points l lines symb_points :=
    print (string_list_of_nats_with_lines_and_points l lines symb_points).
  Goal True.
    print_list (1::5::7::15::nil).
    print_list (1::5::7::30::nil).
    print_list_with_lines (1::5::10::18::nil) (11::nil).
    print_list_with_lines (1::5::10::18::nil) (6::11::nil).
    print_list_with_lines_and_points (1::5::10::18::nil) (6::11::nil) (("o", (1::nil))::("●", (10::nil))::nil).
  Abort.
End NatPrinter.
