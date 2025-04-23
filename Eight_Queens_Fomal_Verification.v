Require Import List Arith Lia.
Import ListNotations.

(* Import board definition and basic functions from brute force version *)
Require Import Eight_Queens_Brute_Force.

(*
A board is represented as a list of natural numbers, where:
- Each element represents a column position
- The index of the element represents the row
- The length of the list represents the board size
*)
Definition board := list nat.

(*
The abs function computes the absolute difference between two natural numbers.
It takes two parameters:
- n: First natural number
- m: Second natural number

Returns the absolute difference between n and m.
*)
Fixpoint abs (n m : nat) : nat :=
  if leb n m then m - n else n - m.

(*
The safe function checks if a queen can be placed in a given column without threatening any other queens.
It takes three parameters:
- col: The column position to check
- rest: The list of existing queen positions (board state)
- row_offset: The distance from the current row being checked

The function returns a Prop (proposition) that is true if:
1. The column is not already occupied by another queen
2. The column is not on the same diagonal as any existing queen
   (diagonal check: |col - c'| ≠ row_offset)
3. The position is safe with respect to all remaining queens

This is a recursive function that checks each existing queen position against the proposed position.
*)
Fixpoint safe (col : nat) (rest : board) (row_offset : nat) : Prop :=
  match rest with
  | [] => True
  | c' :: rest' =>
      col <> c' /\ abs col c' <> row_offset /\ safe col rest' (S row_offset)
  end.

(*
The valid function checks if an entire board configuration is valid.
It takes one parameter:
- b: The board configuration to validate

Returns a Prop that is true if:
1. The board is empty (base case), or
2. The first queen is safe from all other queens, and
3. The rest of the board is also valid

This is a recursive function that validates the entire board configuration.
*)
Fixpoint valid (b : board) : Prop :=
  match b with
  | [] => True
  | c :: rest => safe c rest 1 /\ valid rest
  end.

(*
The safeb function is the boolean version of the safe function.
It takes three parameters:
- col: The column position to check
- rest: The list of existing queen positions
- row_offset: The distance from the current row

Returns a boolean that is true if the position is safe, false otherwise.
This version is used for computation rather than proof.
*)
Fixpoint safeb (col : nat) (rest : board) (row_offset : nat) : bool :=
  match rest with
  | [] => true
  | c' :: rest' =>
      if Nat.eqb col c' then false
      else if Nat.eqb (abs col c') row_offset then false
      else safeb col rest' (S row_offset)
  end.

(*
The validb function is the boolean version of the valid function.
It takes one parameter:
- b: The board configuration to validate

Returns a boolean that is true if the board is valid, false otherwise.
This version is used for computation rather than proof.
*)
Fixpoint validb (b : board) : bool :=
  match b with
  | [] => true
  | c :: rest => safeb c rest 1 && validb rest
  end.

(*
The is_valid_board function is a wrapper around validb.
It takes one parameter:
- b: The board configuration to validate

Returns a boolean indicating if the board is a valid N-Queens solution.
*)
Definition is_valid_board (b : board) : bool := validb b.

(*
The board_length predicate defines what it means for a board to have length n.
It takes two parameters:
- n: The desired length
- b: The board to check

Returns a Prop that is true if the board's length equals n.
*)
Definition board_length n (b : board) := length b = n.

(*
The validb_spec lemma proves the equivalence between the boolean and propositional versions of board validation.
It states that for any board b, validb b = true if and only if valid b.

This is a crucial lemma that connects the computational and logical aspects of the verification.
*)
Definition validb_spec : forall b, validb b = true <-> valid b.
Proof.
  induction b as [|x xs IH]. 
  * simpl. split; auto.
  * simpl. rewrite Bool.andb_true_iff. destruct (IH) as [IH1 IH2].
    split.
    + intros [H1 H2].
      induction xs as [|y ys IHs].
      - simpl in H1. constructor. auto.
      - simpl in H1. repeat (apply andb_prop in H1 as [-> H1]); repeat (apply Bool.negb_true_iff in H1).
        repeat rewrite Nat.eqb_neq in *. rewrite Nat.eqb_eq in *.
        simpl. repeat split; auto.
    + intros [[Hneq Habs] Hval]. 
      rewrite IH2 in Hval. clear IH2.
      revert Hneq Habs. generalize 1.
      induction xs as [|y ys IHs]; intros n0 Hneq Habs.
      - simpl. reflexivity.
      - simpl. rewrite Nat.eqb_neq in Hneq. rewrite Nat.eqb_neq in Habs.
        rewrite Hneq, Habs, IHs; auto.
Qed.

(* Example for N = 4: [2; 4; 1; 3] is a known solution *)
Definition sol4 := [2; 4; 1; 3].

(*
The sol4_valid lemma proves that the example solution for N=4 is valid.
This serves as a concrete example of a valid solution.
*)
Lemma sol4_valid : valid sol4.
Proof.
  unfold sol4. simpl.
  repeat split; compute; lia.
Qed.

(*
The test_sol4 example demonstrates that the boolean validator confirms the validity of sol4.
This provides a computational check of the example solution.
*)
Example test_sol4 : is_valid_board sol4 = true.
Proof. reflexivity. Qed.

(*
The test_invalid example demonstrates that an invalid configuration is correctly rejected.
This provides a negative test case for the validator.
*)
Example test_invalid : is_valid_board [1; 2; 3; 4] = false.
Proof. reflexivity. Qed.

(*
The insert_all function generates all possible ways to insert an element into a list.
It takes two parameters:
- x: The element to insert
- l: The list to insert into

Returns a list of lists, where each list is a different permutation of l with x inserted.
*)
Fixpoint insert_all (x : nat) (l : list nat) : list (list nat) :=
  match l with
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: map (fun zs => y :: zs) (insert_all x ys)
  end.

(*
The perms function generates all possible permutations of a list.
It takes one parameter:
- l: The list to permute

Returns a list of all possible permutations of the input list.
This is a recursive function that uses insert_all to generate permutations.
*)
Fixpoint perms (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | x :: xs => concat (map (insert_all x) (perms xs))
  end.

(*
The range function generates a list of natural numbers from 1 to n.
It takes one parameter:
- n: The upper bound of the range

Returns a list [1; 2; ...; n] in ascending order.
*)
Fixpoint range (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => range n' ++ [n]
  end.

(*
The all_valid_boards function generates all valid N-Queens solutions for a given n.
It takes one parameter:
- n: The size of the board (N×N)

Returns a list of all valid board configurations that solve the N-Queens problem.
It works by:
1. Generating all possible permutations of column positions
2. Filtering to keep only valid configurations
*)
Definition all_valid_boards (n : nat) : list board :=
  filter is_valid_board (perms (range n)).

(*
The n_queens_solutions function is a wrapper around all_valid_boards.
It takes one parameter:
- n: The size of the board (N×N)

Returns all valid solutions to the N-Queens problem for an N×N board.
This function provides a clean interface to get all solutions.
*)
Definition n_queens_solutions (n : nat) : list board :=
  all_valid_boards n.

(*
The safe_partial function is an optimized version of safeb for the backtracking solution.
It takes three parameters:
- col: The column position to check
- queens: The list of existing queen positions
- row_offset: The distance from the current row

Returns a boolean that is true if the position is safe, false otherwise.
This version uses a more efficient implementation with orb for early termination.
*)
Fixpoint safe_partial (col : nat) (queens : board) (row_offset : nat) : bool :=
  match queens with
  | [] => true
  | c' :: qs =>
      if (Nat.eqb col c' || Nat.eqb (abs col c') row_offset)%nat
      then false
      else safe_partial col qs (S row_offset)
  end.

(*
The solve_nqueens function implements a backtracking solution to the N-Queens problem.
It takes three parameters:
- n: The size of the board (N×N)
- k: The number of queens left to place
- partial: The current partial solution

Returns a list of all valid solutions that can be built from the partial solution.
This function:
1. Uses safe_partial to check potential queen placements
2. Recursively builds solutions by trying each valid column position
3. Uses flat_map to combine all valid solutions
*)
Fixpoint solve_nqueens (n k : nat) (partial : board) : list board :=
  match k with
  | 0 => [partial]
  | S k' =>
      flat_map (fun col =>
        if safe_partial col partial 1
        then solve_nqueens n k' (col :: partial)
        else []) (seq 1 n)
  end.

(*
The n_queens_fast function is the entry point for the efficient backtracking solution.
It takes one parameter:
- n: The size of the board (N×N)

Returns all valid solutions to the N-Queens problem for an N×N board.
This function uses the backtracking approach which is more efficient than the brute force method.
*)
Definition n_queens_fast (n : nat) : list board :=
  solve_nqueens n n [].

(*
The validb_valid lemma proves that if the boolean validator returns true, then the board is valid.
This is one direction of the validb_spec equivalence.
*)
Lemma validb_valid : forall b, validb b = true -> valid b.
Proof.
  intros b H. apply validb_spec. exact H.
Qed.

(*
The valid_validb lemma proves that if a board is valid, then the boolean validator returns true.
This is the other direction of the validb_spec equivalence.
*)
Lemma valid_validb : forall b, valid b -> validb b = true.
Proof.
  intros b H. apply validb_spec. exact H.
Qed.

(*
The solve_nqueens_correct lemma proves that the backtracking solution generates only valid boards of the correct length.
It states that for any board b in the solution set of n_queens_fast n:
1. The board is valid (valid b)
2. The board has the correct length (length b = n)

This is a crucial correctness property of the backtracking algorithm.
*)
Lemma solve_nqueens_correct : forall n b,
  In b (n_queens_fast n) -> valid b /\ length b = n.
Proof.
  intros n b.
  unfold n_queens_fast.
  generalize dependent b.
  induction n as [|n' IH]; intros b Hb.
  - simpl in Hb. destruct Hb as [Hb | []]. subst. split; simpl; auto.
  - simpl in Hb.
    unfold seq in Hb.
    remember (flat_map _ (seq 1 (S n'))) as boards.
    induction (seq 1 (S n')) as [|c cs IHcs]. simpl in Hb. contradiction.
    simpl in Hb. apply in_app_or in Hb as [Hleft | Hright].
    + destruct (safe_partial c [] 1) eqn:Hsafe.
      * simpl in Hleft. apply IH in Hleft as [Hval Hlen].
        split.
        -- simpl. apply Hval.
        -- simpl. rewrite Hlen. reflexivity.
      * simpl in Hleft. contradiction.
    + apply IHcs in Hright. exact Hright.
Qed.

(*
The in_perms_range lemma proves properties of boards generated by permuting the range.
It states that for any board b in perms (range n):
1. The board has length n
2. The board has no duplicate elements (NoDup)
3. All elements are between 1 and n inclusive

This lemma is used to establish properties of potential solutions.
*)
Lemma in_perms_range : forall n b,
  In b (perms (range n)) -> length b = n /\ NoDup b /\ Forall (fun x => 1 <= x <= n) b.
Proof.
  intros n b.
  induction n as [|n' IH]; intros H.
  - simpl in H. destruct H as [H | []]. subst. simpl. repeat split; constructor.
  - simpl in H. apply in_concat_map_inv in H as [xs [Hxs Hinx]].
    apply IH in Hinx as [Hlen [Hnd Hbound]].
    destruct (in_insert_all_inv _ _ _ Hxs) as [Hins Hlen'].
    subst. repeat split.
    + simpl. lia.
    + inversion Hnd; subst. constructor; auto.
      intro Hin. apply H0. apply in_map with (f := fun zs => y :: zs) in Hin. exact Hin.
    + constructor; auto.
Qed.

(*
The equivalent_solutions lemma proves that the brute force and backtracking solutions are equivalent.
It states that for any board b and size n:
b is in n_queens_solutions n if and only if b is in n_queens_fast n.

This is a crucial correctness property that ensures both methods produce the same set of solutions.
*)
Lemma equivalent_solutions : forall n b,
  In b (n_queens_solutions n) <-> In b (n_queens_fast n).
Proof.
  intros n b.
  split.
  - intros Hin.
    unfold n_queens_solutions, all_valid_boards, is_valid_board in Hin.
    apply filter_In in Hin as [Hperm Hvb].
    apply validb_valid in Hvb.
    (* We'll reconstruct this board by backtracking *)
    assert (length b = n /\ NoDup b /\ Forall (fun x => 1 <= x <= n) b).
    { apply in_perms_range. exact Hperm. }
    destruct H as [Hlen _].
    (* Now show that any valid board is generated by solve_nqueens *)
    (* We build an induction on length of b *)
    revert b Hvb Hlen. induction n as [|n' IH]; intros b Hval Hlen.
    + destruct b; simpl in *; try discriminate. now left.
    + destruct b as [|c rest]; simpl in *; try discriminate.
      simpl.
      remember (safe_partial c rest 1) as sc.
      assert (safe_partial c rest 1 = true).
      { rewrite <- Heqsc. apply valid_validb. exact Hval. }
      rewrite H. simpl.
      apply in_flat_map. exists c. split.
      * apply in_seq. lia.
      * apply IH; simpl in Hlen; lia.
  - intros Hin.
    apply solve_nqueens_correct in Hin as [Hvalid Hlen].
    apply valid_validb in Hvalid.
    apply filter_In. split.
    + apply in_perms_range. unfold n_queens_solutions, all_valid_boards. apply in_seq. lia.
    + exact Hvalid.
Qed.
