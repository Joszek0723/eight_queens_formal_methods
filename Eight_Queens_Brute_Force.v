Require Import List Arith Lia.
Import ListNotations.

(* A board is a list of column indices; index is the row *)
Definition board := list nat.

Definition abs (n m : nat) : nat :=
  if leb n m then m - n else n - m.

Fixpoint safe (col : nat) (rest : board) (row_offset : nat) : Prop :=
  match rest with
  | [] => True
  | c' :: rest' =>
      col <> c' /\ abs col c' <> row_offset /\ safe col rest' (S row_offset)
  end.

Fixpoint valid (b : board) : Prop :=
  match b with
  | [] => True
  | c :: rest => safe c rest 1 /\ valid rest
  end.

Fixpoint safeb (col : nat) (rest : board) (row_offset : nat) : bool :=
  match rest with
  | [] => true
  | c' :: rest' =>
      if Nat.eqb col c' then false
      else if Nat.eqb (abs col c') row_offset then false
      else safeb col rest' (S row_offset)
  end.

Fixpoint validb (b : board) : bool :=
  match b with
  | [] => true
  | c :: rest => safeb c rest 1 && validb rest
  end.

Definition is_valid_board (b : board) : bool := validb b.

(* Example for N = 4: [2; 4; 1; 3] is a known solution *)
Definition sol4 := [2; 4; 1; 3].

Lemma sol4_valid : valid sol4.
Proof.
  unfold sol4. simpl.
  repeat split; compute; lia.
Qed.

Example test_sol4 : is_valid_board sol4 = true.
Proof. reflexivity. Qed.

Example test_invalid : is_valid_board [1; 2; 3; 4] = false.
Proof. reflexivity. Qed.

(* Generate all permutations of a list *)
Fixpoint insert_all (x : nat) (l : list nat) : list (list nat) :=
  match l with
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: map (fun zs => y :: zs) (insert_all x ys)
  end.

Fixpoint perms (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | x :: xs => concat (map (insert_all x) (perms xs))
  end.

(* Generate [1; 2; ...; n] *)
Fixpoint range (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => range n' ++ [n]
  end.

Definition all_valid_boards (n : nat) : list board :=
  filter is_valid_board (perms (range n)).

(* Print all solutions for N = 4 *)
Eval compute in all_valid_boards 4.

(* Arbitrary N support: *)
Definition n_queens_solutions (n : nat) : list board :=
  all_valid_boards n.

(* You can now compute for any n: *)
(* Eval compute in n_queens_solutions 5. *)

(* You can use Extraction to OCaml for actual performance *)
