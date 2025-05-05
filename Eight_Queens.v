Require Import List Arith Lia.
From Coq Require Import List Permutation Bool.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

(**
  * N-Queens Formal Verification
  * 
  * This file contains formal verification of the N-Queens problem using Coq.
  * We implement and verify two main approaches:
  * 1. A brute force approach that generates all permutations and filters valid ones
  * 2. A backtracking approach that incrementally builds valid solutions
  *)

(**
  * Brute Force Solution 
  *
  * The brute force approach works by:
  * 1. Generating all possible permutations of queen placements
  * 2. Filtering them to keep only valid ones
  * 3. A valid placement ensures no queens attack each other
  *)

(**
  * [board] represents a chess board configuration for the N-Queens problem.
  * Each element represents a column position, and the index represents the row.
  * The length of the list represents the board size.
  * 
  * For example, [2; 4; 1; 3] represents a 4×4 board where:
  * - Row 1 has a queen in column 2
  * - Row 2 has a queen in column 4
  * - Row 3 has a queen in column 1
  * - Row 4 has a queen in column 3
  *)
Definition board := list nat.

(**
  * [abs n m] computes the absolute difference between two natural numbers.
  * 
  * This function is essential for checking diagonal attacks in the N-Queens problem.
  * Two queens attack each other diagonally if the absolute difference in their row 
  * positions equals the absolute difference in their column positions.
  *
  * @param n The first natural number
  * @param m The second natural number
  * @return The absolute difference |n - m|
  *)
  Definition abs (n m : nat) : nat :=
  if Nat.leb n m
  then m - n
  else n - m.

(**
  * [safeb col rest row_offset] checks if a queen at column [col] is safe 
  * with respect to the queens in [rest], starting at row offset [row_offset].
  *
  * A queen is safe if it doesn't attack any other queen, meaning:
  * 1. It's not in the same column as any other queen
  * 2. It's not on the same diagonal as any other queen
  *
  * @param col The column position to check
  * @param rest The list of existing queen positions
  * @param row_offset The row distance from the current position
  * @return true if the position is safe, false otherwise
  *)
Fixpoint safeb (col : nat) (rest : board) (row_offset : nat) : bool :=
  match rest with
  | [] => true
  | c' :: rest' =>
      negb (Nat.eqb col c' || Nat.eqb (abs col c') row_offset)
      && safeb col rest' (S row_offset)
  end.

(**
  * [validb b] checks if a board configuration is valid.
  *
  * A valid board has no attacking queens. This function checks each queen
  * against all queens placed after it in the list to ensure there are no attacks.
  *
  * @param b The board configuration to validate
  * @return true if the board is valid, false otherwise
  *)
Fixpoint validb (b : board) : bool :=
  match b with
  | [] => true
  | c :: rest => safeb c rest 1 && validb rest
  end.

(**
  * [safe col rest row_offset] is the propositional version of [safeb].
  *
  * This lifts the boolean safety check to the Prop universe for use in formal proofs.
  *
  * @param col The column position to check
  * @param rest The list of existing queen positions
  * @param row_offset The row distance from the current position
  * @return A proposition that the position is safe
  *)
Definition safe (col : nat) (rest : board) (row_offset : nat) : Prop :=
  safeb col rest row_offset = true.

(**
  * [valid b] is the propositional version of [validb].
  *
  * This lifts the boolean board validation to the Prop universe for use in formal proofs.
  *
  * @param b The board configuration to validate
  * @return A proposition that the board is valid
  *)
Definition valid (b : board) : Prop :=
  validb b = true.

(**
  * [safeb_correct] establishes the equivalence between the [safe] proposition
  * and the [safeb] boolean function.
  *
  * This lemma is straightforward since [safe] is defined directly in terms of [safeb].
  *
  * @param col The column position to check
  * @param rest The list of existing queen positions
  * @param offset The row distance from the current position
  * @return A proof that safe col rest offset <-> safeb col rest offset = true
  *)
Lemma safeb_correct col rest offset :
  safe col rest offset <-> safeb col rest offset = true.
Proof. reflexivity. Qed.

(**
  * [validb_correct] establishes the equivalence between the [valid] proposition
  * and the [validb] boolean function.
  *
  * This lemma is straightforward since [valid] is defined directly in terms of [validb].
  *
  * @param b The board configuration to validate
  * @return A proof that valid b <-> validb b = true
  *)
Lemma validb_correct b :
  valid b <-> validb b = true.
Proof. reflexivity. Qed.

(**
  * [sol4] defines a known solution to the 4-Queens problem.
  *
  * The solution [2; 4; 1; 3] represents a valid placement of queens on a 4×4 board,
  * with queens placed at positions:
  * - Row 1, Column 2
  * - Row 2, Column 4
  * - Row 3, Column 1
  * - Row 4, Column 3
  *)
Definition sol4 := [2; 4; 1; 3].

(**
  * [sol4_valid] formally proves that [sol4] is a valid solution to the 4-Queens problem.
  *
  * This lemma verifies that the known solution [2; 4; 1; 3] satisfies the validity
  * constraints of the n-queens problem, ensuring no queens attack each other.
  *)
Lemma sol4_valid : valid sol4.
Proof. unfold sol4, valid. simpl. reflexivity. Qed.

(**
  * [test_sol4] is an example demonstrating that [sol4] is valid.
  *
  * This example explicitly computes the result of [validb sol4] to show
  * it evaluates to true, confirming the validity of the solution.
  *)
Example test_sol4 : validb sol4 = true.
Proof. reflexivity. Qed.

(**
  * [test_invalid] is an example demonstrating an invalid board configuration.
  *
  * The configuration [1; 2; 3; 4] is invalid because queens can attack each other.
  * Specifically, queens on the diagonal can attack each other.
  *)
Example test_invalid : validb [1; 2; 3; 4] = false.
Proof. reflexivity. Qed.

(**
  * [insert_all x l] generates all possible ways to insert an element [x]
  * into a list [l] at all possible positions.
  *
  * This function is used by the permutation generator to create all permutations.
  * It systematically inserts an element at each possible position in the list.
  *
  * @param x The element to insert
  * @param l The list to insert into
  * @return A list of lists, where each list is a different result of inserting x into l
  *)
Fixpoint insert_all (x : nat) (l : list nat) : list (list nat) :=
  match l with
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: map (fun zs => y :: zs) (insert_all x ys)
  end.

(**
  * [perms l] generates all possible permutations of a list [l].
  *
  * This function works recursively:
  * 1. For the empty list, there's only one permutation: the empty list
  * 2. For a non-empty list, it takes the first element, finds all permutations 
  *    of the rest, and then inserts the first element at all possible positions
  *    in each of those permutations
  *
  * @param l The list to permute
  * @return A list of all possible permutations of [l]
  *)
Fixpoint perms (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | x :: xs => concat (map (insert_all x) (perms xs))
  end. 

(**
  * [range n] generates a list of natural numbers from 1 to n in ascending order.
  *
  * For the N-Queens problem, this function generates the column positions
  * that can be used in a solution for an n×n board.
  *
  * @param n The upper bound of the range
  * @return The list [1; 2; ...; n]
  *)
Fixpoint range (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => range n' ++ [n]
  end.

(**
  * [all_valid_boards n] generates all valid solutions to the N-Queens problem
  * for an n×n board using the brute force approach.
  *
  * The function works by:
  * 1. Generating all possible permutations of column positions (1 to n)
  * 2. Filtering to keep only those permutations that represent valid board configurations
  *
  * @param n The size of the board (n×n)
  * @return A list of all valid n-queens solutions
  *)
Definition all_valid_boards (n : nat) : list board :=
  filter validb (perms (range n)).

(* Print all solutions for N = 1 *)
Eval compute in all_valid_boards 1.

(* Print all solutions for N = 2 *)
Eval compute in all_valid_boards 2.

(* Print all solutions for N = 3 *)
Eval compute in all_valid_boards 3.

(* Print all solutions for N = 4 *)
Eval compute in all_valid_boards 4.

(* Print all solutions for N = 5 *)
Eval compute in (length (all_valid_boards 5), all_valid_boards 5).

(* Print all solutions for N = 6 *)
Eval compute in (length (all_valid_boards 6), all_valid_boards 6).

(* Print all solutions for N = 7 *)
Eval compute in (length (all_valid_boards 7), all_valid_boards 7).

(* Print all solutions for N = 8 and count them *)
Eval compute in (length (all_valid_boards 8), all_valid_boards 8).

(**
  * [n_queens_brute_force n] is a wrapper around [all_valid_boards] that 
  * returns all valid solutions to the N-Queens problem for an n×n board.
  *
  * This function provides a clean interface to access all valid solutions
  * using the brute force approach.
  *
  * @param n The size of the board (n×n)
  * @return A list of all valid n-queens solutions
  *)
Definition n_queens_brute_force (n : nat) : list board :=
  all_valid_boards n.

(**
  * Correctness of the Brute-Force Solver
  *
  * We now prove the factual correctness of our brute-force n-queens algorithm.
  * This requires establishing two key properties:
  *
  * 1. Soundness: Every board returned by the algorithm is indeed a valid n-queens solution.
  * 2. Completeness: Every valid n-queens solution of size n is found by the algorithm.
  *)

(**
  * [brute_force_sound] proves the soundness of the brute force algorithm.
  *
  * This lemma establishes that every board returned by the n_queens_brute_force
  * function is a valid n-queens solution, ensuring there are no attacking queens.
  *
  * @param n The size of the board (n×n)
  * @param b A board configuration returned by the brute force algorithm
  * @return A proof that b is a valid board configuration
  *)
Lemma brute_force_sound n b :
  In b (n_queens_brute_force n) ->
  validb b = true.
Proof.
  unfold n_queens_brute_force, all_valid_boards.
  intros Hin; apply filter_In in Hin as [_ Hvalid]; exact Hvalid.
Qed.

(**
  * [in_insert_all] characterizes the shape of any list produced by [insert_all x l].
  *
  * This lemma shows that every list produced by insert_all decomposes as [l1 ++ x :: l2],
  * where [l1 ++ l2] is a permutation of the original list [l]. This is a key property
  * used in proving the correctness of the permutation generator.
  *
  * @param x The element being inserted
  * @param l The original list
  * @param l' A list produced by insert_all x l
  * @return A proof characterizing the structure of l' in terms of l and x
  *)
Lemma in_insert_all : forall x l l',
  In l' (insert_all x l) ->
  exists l1 l2, l' = l1 ++ x :: l2 /\ Permutation (l1 ++ l2) l.
Proof.
  intros x l l' Hin.
  induction l as [|y ys IH] in l', Hin |- *.
  - simpl in Hin. destruct Hin as [H|H]; [|contradiction].
    subst l'. exists [], []. split; auto.
  - simpl in Hin. destruct Hin as [H|H].
    + subst l'. exists [], (y::ys). split; auto.
    + apply in_map_iff in H. destruct H as [zs [Heq Hzs]].
      apply IH in Hzs. destruct Hzs as [l1 [l2 [Heq' Hperm]]].
      subst zs.
      exists (y::l1), l2. split.
      * rewrite <- Heq. simpl. reflexivity.
      * apply Permutation_cons. reflexivity. assumption.
Qed.

(**
  * [perms_sound] proves the soundness of the permutation generator.
  *
  * This lemma establishes that every list produced by the [perms] function
  * is a permutation of the original list. This is a key property for ensuring
  * that the brute force approach considers all valid board arrangements.
  *
  * @param l The original list
  * @param l' A list produced by perms l
  * @return A proof that l' is a permutation of l
  *)
Lemma perms_sound : forall l l', In l' (perms l) -> Permutation l l'.
Proof.
  induction l as [|a l IHl]; intros l' Hin.
  - simpl in Hin. destruct Hin as [H | H]; [subst l'; apply Permutation_refl | contradiction].
  - simpl in Hin. 
    apply in_concat in Hin. destruct Hin as [l'' [Hin1 Hin2]].
    apply in_map_iff in Hin1. destruct Hin1 as [l''' [Heq Hin1]].
    subst l''.
    apply IHl in Hin1. 
    clear IHl.
    generalize dependent l'.
    induction l''' as [|x xs IH] in a, Hin1 |- *.
    + simpl. intros l' Hin2.
      destruct Hin2 as [H|H]; [subst l' | contradiction].
      simpl. apply Permutation_cons. reflexivity. apply Hin1.
    + simpl. intros l' Hin2.
      destruct Hin2 as [H|H].
      * subst l'. apply Permutation_cons. reflexivity. assumption.
      *apply in_map_iff in H. destruct H as [zs [Heq' Hzs]].
        apply in_insert_all in Hzs. destruct Hzs as [l1 [l2 [Heq'' Hperm]]].
        subst zs l'.
        apply Permutation_trans with (a :: x :: l1 ++ l2). 
        apply Permutation_cons. reflexivity. 
        apply Permutation_trans with (x :: xs).
          ** apply Hin1.
          ** apply perm_skip. apply Permutation_sym, Hperm.
          ** 
          apply Permutation_trans with (x :: a :: l1 ++ l2).
            *** apply perm_swap. 
            *** apply perm_skip. 
                apply Permutation_cons_app. 
                apply Permutation_refl.
Qed.

(**
  * [insert_all_head] proves that inserting an element at the head is always
  * one of the results produced by the [insert_all] function.
  *
  * This lemma shows that for any element [a] and list [l2], the list [a :: l2]
  * (where a is inserted at the beginning) is always one of the results produced
  * by [insert_all a l2]. This is used in proving the completeness of the
  * permutation generator.
  *
  * @param a The element to insert
  * @param l2 The list to insert into
  * @return A proof that (a :: l2) is in (insert_all a l2)
  *)
Lemma insert_all_head : forall a l2, In (a :: l2) (insert_all a l2).
Proof.
  intros.
  induction l2 as [|y ys IH].
  - simpl. left. reflexivity.
  - simpl. left. reflexivity.
Qed.

(**
  * [perms_complete] proves the completeness of the permutation generator.
  *
  * This lemma establishes that every possible permutation of a list [l]
  * appears in the result of [perms l]. Combined with [perms_sound], this
  * shows that [perms l] generates exactly all permutations of [l], no more
  * and no less.
  *
  * @param l The original list
  * @param l' A permutation of l
  * @return A proof that l' is in (perms l)
  *)
Lemma perms_complete : forall l l', Permutation l l' -> In l' (perms l).
Proof.
  induction l; intros l' Hperm.
  - simpl.
    apply Permutation_nil in Hperm.
    subst l'.
    left; reflexivity.
  - simpl.
    assert (In a l') as Ha.
    { apply Permutation_in with (x := a) in Hperm; [| left; reflexivity].
      assumption. }
    destruct (in_split a l') as [l1 [l2 Hl']]; [assumption|].
    subst l'.
    apply Permutation_cons_app_inv in Hperm.
    apply in_concat.
    exists (insert_all a (l1 ++ l2)).
    split.
    + apply in_map. apply IHl. apply Hperm.
    + clear IHl Hperm.
      induction l1 as [|x l1 IH].
      * apply insert_all_head.
      * simpl.
        right.
        apply in_map.
        apply IH.
        simpl in Ha.
        destruct Ha as [Hax | Ha'].
        -- subst x. apply in_or_app. right. simpl. left. reflexivity.
        -- assumption.
Qed.

(**
  * [brute_force_complete] proves the completeness of the brute force algorithm.
  *
  * This theorem establishes that any valid n-queens solution of size n
  * is found by the brute force algorithm. Specifically, any board that has:
  * 1. Length n
  * 2. Valid queen placements (no attacks)
  * 3. A permutation of the range 1..n
  * will be returned by n_queens_brute_force.
  *
  * @param n The size of the board (n×n)
  * @param b A valid board configuration of length n
  * @return A proof that b is in the results of n_queens_brute_force n
  *)
Theorem brute_force_complete n b :
  length b = n ->
  valid b ->
  Permutation b (range n) ->
  In b (n_queens_brute_force n).
Proof.
  unfold n_queens_brute_force, all_valid_boards.
  intros Hlen Hvalid Hperm.
  apply filter_In.
  split.
  - apply perms_complete.
    apply Permutation_sym, Hperm.  
  - apply Hvalid.
Qed.

(**
  * [range_length] proves that the length of [range n] is exactly n.
  *
  * This lemma establishes a basic property of the range function,
  * which is essential for reasoning about the size of boards and permutations
  * in the n-queens problem.
  *
  * @param n The upper bound of the range
  * @return A proof that length (range n) = n
  *)
Lemma range_length : forall n, length (range n) = n.
Proof.
  induction n as [|n IH].
  - simpl; reflexivity.
  - simpl range. rewrite app_length, IH. simpl. rewrite Nat.add_comm. reflexivity.
Qed.

(**
  * [brute_force_correct] establishes the full correctness of the brute force solver.
  *
  * This theorem combines soundness and completeness to show that the brute force
  * algorithm returns exactly the boards that are:
  * 1. Of length n
  * 2. Valid (no attacking queens)
  * 3. Permutations of the range 1..n
  *
  * This characterizes the precise set of solutions returned by the algorithm.
  *
  * @param n The size of the board (n×n)
  * @param b A board configuration
  * @return A proof of the bidirectional implication between
  *         In b (n_queens_brute_force n) and (length b = n ∧ valid b ∧ Permutation b (range n))
  *)
Theorem brute_force_correct n b :
  In b (n_queens_brute_force n) <->
  (length b = n /\ valid b /\ Permutation b (range n)).
Proof.
  split.
  - intros Hin.
    split; [| split].
    + unfold n_queens_brute_force, all_valid_boards in Hin.
      apply filter_In in Hin as [Hperm Hvalid].
      apply perms_sound in Hperm.
      apply Permutation_length in Hperm.
      rewrite range_length in Hperm.  
      symmetry; assumption.
    + unfold valid. 
      apply brute_force_sound with (n := n).
      assumption.
    + unfold n_queens_brute_force, all_valid_boards in Hin.
      apply filter_In in Hin as [Hperm _].
      apply perms_sound in Hperm.
      apply Permutation_sym; assumption.
  - intros [Hlen [Hvalid Hperm]].
    apply brute_force_complete; assumption.
Qed.

(*
  *** Efficent Solution ***
*)

(**
  * Efficient Backtracking Solution
  *
  * The backtracking approach is significantly more efficient than the brute force method.
  * Instead of generating all possible queen placements and then checking which ones are valid,
  * it incrementally builds solutions by:
  * 1. Placing queens column by column
  * 2. Only considering safe placements at each step
  * 3. Recursively building solutions from valid partial placements
  *)

(**
  * [safeb_efficient] is an optimized version of [safeb] for the backtracking solution.
  *
  * This function checks if a queen at column [col] is safe with respect to queens in
  * [queens], starting at row offset [row_offset]. It uses early termination with
  * a boolean OR operation to stop checking as soon as a conflict is detected.
  *
  * @param col The column position to check
  * @param queens The list of existing queen positions
  * @param row_offset The row distance from the current position
  * @return true if the position is safe, false otherwise
  *)
Fixpoint safeb_efficient (col : nat) (queens : board) (row_offset : nat) : bool :=
  match queens with
  | [] => true
  | c' :: qs =>
      if orb (Nat.eqb col c') (Nat.eqb (abs col c') row_offset)
      then false
      else safeb_efficient col qs (S row_offset)
  end.

(**
  * [safeb_efficient_equiv] proves that [safeb_efficient] and [safeb] are equivalent.
  *
  * This lemma establishes that the optimized safety check function returns the same
  * result as the original safety check, ensuring that the optimization preserves correctness.
  *
  * @param col The column position to check
  * @param qs The list of existing queen positions
  * @param offset The row distance from the current position
  * @return A proof that safeb_efficient col qs offset = safeb col qs offset
  *)
Lemma safeb_efficient_equiv col qs offset :
  safeb_efficient col qs offset = safeb col qs offset.
Proof.
  generalize dependent offset.
  induction qs as [| q qs IH]; simpl.
  - intros offset.
    reflexivity.
  - intros offset.
    destruct (orb (Nat.eqb col q) (Nat.eqb (abs col q) offset)) eqn:E; simpl.
    + reflexivity.
    + apply IH.
Qed.

(**
  * [solve_nqueens] implements the backtracking algorithm for the N-Queens problem.
  *
  * This function builds valid solutions incrementally by placing queens column by column.
  * For each column, it checks all possible row placements and recursively extends only
  * those that don't create conflicts with previously placed queens.
  *
  * @param n The size of the board (n×n)
  * @param k The number of queens left to place
  * @param partial The current partial solution (queens already placed)
  * @return A list of all valid complete solutions that can be built from partial
  *)
Fixpoint solve_nqueens (n k : nat) (partial : board) : list board :=
  match k with
  | 0 => [partial]
  | S k' =>
      flat_map (fun col =>
        if safeb_efficient col partial 1
        then solve_nqueens n k' (col :: partial)
        else []) (seq 1 n)
  end.

(**
  * [n_queens_backtracking] is the entry point for the efficient backtracking solution.
  *
  * This function solves the N-Queens problem for an n×n board using the backtracking
  * approach, which is significantly more efficient than the brute force method.
  *
  * @param n The size of the board (n×n)
  * @return A list of all valid n-queens solutions
  *)
Definition n_queens_backtracking (n : nat) : list board :=
  solve_nqueens n n [].

(* Test the efficient method *)
Eval compute in n_queens_backtracking 4.

(**
  * [valid_column_extension] proves that adding a safe column to a valid board maintains validity.
  *
  * This lemma is fundamental to the backtracking approach. It establishes that if we have
  * a valid board [b] and a column placement [col] that is safe with respect to [b],
  * then the extended board [col :: b] is also valid.
  *
  * @param b The existing valid partial board
  * @param col The new column to add
  * @param Hvalid A proof that b is valid
  * @param Hsafe A proof that col is safe with respect to b
  * @return A proof that (col :: b) is valid
  *)
Lemma valid_column_extension : forall b col,
  valid b -> safeb_efficient col b 1 = true -> valid (col :: b).
Proof.
  intros b col Hvalid Hsafe.
  unfold valid in *. 
  simpl.
  apply andb_true_iff. split.
  - rewrite <- safeb_efficient_equiv. 
    exact Hsafe. 
  - exact Hvalid.
Qed.

(**
  * [solve_nqueens_sound] proves the soundness of the backtracking algorithm.
  *
  * This lemma establishes that every board returned by the [solve_nqueens] function
  * is valid (no queens attack each other). It shows that if we start with a valid
  * partial solution, all complete solutions built from it will also be valid.
  *
  * @param n The size of the board (n×n)
  * @param k The number of queens left to place
  * @param partial The current partial solution
  * @param Hvalid_partial A proof that partial is valid
  * @param b A board in the result of solve_nqueens
  * @return A proof that b is valid
  *)
Lemma solve_nqueens_sound : forall n k partial,
  valid partial ->
  forall b, In b (solve_nqueens n k partial) -> valid b.
Proof.
  induction k as [|k' IHk]; intros partial Hvalid_partial b Hin.
  - simpl in Hin. destruct Hin as [Heq|Hfalse]; [|contradiction].
    subst b. exact Hvalid_partial.
  - simpl in Hin.
    apply in_flat_map in Hin as [col [Hin_col Hin_b]].
    destruct (safeb_efficient col partial 1) eqn:Hsafe.
    + assert (valid (col :: partial)) as Hvalid_extended.
      { apply valid_column_extension; assumption. }
      apply IHk with (partial := col :: partial); assumption.
    + simpl in Hin_b.
      contradiction.
Qed.

(**
  * [backtracking_sound] proves the soundness of the overall backtracking solution.
  *
  * This theorem establishes that every board returned by the [n_queens_backtracking]
  * function is a valid n-queens solution (no queens attack each other).
  *
  * @param n The size of the board (n×n)
  * @param b A board in the result of n_queens_backtracking
  * @return A proof that b is valid
  *)
Theorem backtracking_sound : forall n b,
  In b (n_queens_backtracking n) -> valid b.
Proof.
  intros n b Hin.
  unfold n_queens_backtracking in Hin.
  apply solve_nqueens_sound with (n := n) (k := n) (partial := []); auto.
  unfold valid, validb. simpl. reflexivity.
Qed.

+(**
+ * [brute_force_count n] counts the total number of configurations examined
+ * by the brute force algorithm for an n×n board.
+ *
+ * This function directly measures the size of the search space explored
+ * by the brute force approach, which is equal to the number of all possible
+ * permutations of column positions 1 to n.
+ *
+ * @param n The size of the board (n×n)
+ * @return The number of configurations examined (n!)
+ *)
Definition brute_force_count (n : nat) : nat :=
  length (perms (range n)).

+(**
+ * [sumn l] computes the sum of all natural numbers in a list.
+ *
+ * This helper function is used to calculate the total number of
+ * configurations examined by the backtracking algorithm.
+ *
+ * @param l A list of natural numbers
+ * @return The sum of all elements in the list
+ *)
(* Sum of a list of nats *)
Fixpoint sumn (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sumn xs
  end.

+(**
+ * [solve_nqueens_count n k partial] counts the total number of configurations
+ * examined when solving the N-Queens problem using backtracking.
+ *
+ * This function works similarly to the regular solve_nqueens, but instead of
+ * collecting solutions, it counts the number of positions examined, including
+ * both successful placements and pruned branches.
+ *
+ * @param n The size of the board (n×n)
+ * @param k The number of queens left to place
+ * @param partial The current partial solution (queens already placed)
+ * @return The number of configurations examined from this position
+ *)
Fixpoint solve_nqueens_count (n k : nat) (partial : board) : nat :=
  match k with
  | 0 => 1 (* Count completed boards *)
  | S k' =>
      sumn (map (fun col =>
        if safeb_efficient col partial 1
        then solve_nqueens_count n k' (col :: partial)
        else 1 (* Count pruned branches as 1 exploration *)
      ) (seq 1 n))
  end.

+(**
+ * [backtracking_count n] counts the total number of configurations examined
+ * by the backtracking algorithm for an n×n board.
+ *
+ * This function measures the size of the search space explored by the
+ * backtracking approach, which is significantly smaller than the brute
+ * force approach due to early pruning of invalid configurations.
+ *
+ * @param n The size of the board (n×n)
+ * @return The number of configurations examined
+ *)
Definition backtracking_count (n : nat) : nat :=
  solve_nqueens_count n n [].

Eval compute in brute_force_count 8.
Eval compute in backtracking_count 8.