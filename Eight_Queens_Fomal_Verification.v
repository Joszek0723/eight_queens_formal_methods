Require Import List Arith Lia.
Import ListNotations.

(* Import board definition and basic functions from brute force version *)
Require Import eight_queens_formal_methods.Eight_Queens.


(* First, let's prove the helper lemmas *)

(* Helper lemma: safe_partial is equivalent to the propositional safe *)
Lemma safe_partial_correct col rest offset :
  safe col rest offset <-> safe_partial col rest offset = true.
Proof.
  split.
  - (* Forward direction: safe -> safe_partial = true *)
    revert offset. induction rest as [|c' rest IH]; intros offset.
    + (* Base case: empty list *)
      reflexivity.
    + (* Inductive case *)
      simpl. intros [H1 [H2 H3]].
      rewrite IH by assumption.
      rewrite <- Nat.eqb_neq in H1. rewrite H1.
      rewrite <- Nat.eqb_neq in H2. rewrite H2.
      reflexivity.
  
  - (* Backward direction: safe_partial = true -> safe *)
    revert offset. induction rest as [|c' rest IH]; intros offset.
    + (* Base case: empty list *)
      reflexivity.
    + (* Inductive case *)
      simpl. destruct (col =? c') eqn:Ec; try discriminate.
      destruct (abs col c' =? offset) eqn:Ea; try discriminate.
      intros Hsafe.
      (* Convert boolean equalities to inequalities *)
      apply Nat.eqb_neq in Ec.  (* (col =? c') = false -> col <> c' *)
      apply Nat.eqb_neq in Ea.  (* (abs col c' =? offset) = false -> abs col c' <> offset *)
      split; [exact Ec|].
      split; [exact Ea|].
      apply IH.
      exact Hsafe.
Qed.

(* Helper lemma: solutions from solve_nqueens are valid *)
Lemma solve_nqueens_safe n k partial :
  Forall (fun b => valid b) (solve_nqueens n k partial).
Proof.
  revert partial.
  induction k as [|k IH]; intros partial; simpl.
  - constructor. constructor.
  - apply Forall_flat_map. intros col.
    destruct (safe_partial col partial 1) eqn:Hsafe.
    + constructor. intros b Hb. apply IH.
    + constructor.
Qed.

(* Helper lemma: solve_nqueens produces permutations of [1..n] *)
Lemma solve_nqueens_permutation n k partial :
  Forall (fun b => Permutation (partial ++ range k) b) (solve_nqueens n k partial).
Proof.
  revert partial.
  induction k as [|k IH]; intros partial; simpl.
  - constructor. rewrite app_nil_r. apply Permutation_refl.
  - apply Forall_flat_map. intros col.
    destruct (safe_partial col partial 1) eqn:Hsafe.
    + constructor. intros b Hb. specialize (IH (col :: partial)).
      apply Forall_forall in IH. apply IH in Hb.
      simpl in Hb. rewrite <- app_assoc in Hb. simpl in Hb.
      apply Permutation_cons_app. auto.
    + constructor.
Qed.

(* Helper lemma: any valid solution is found by solve_nqueens *)
Lemma solve_nqueens_complete n b :
  length b = n -> valid b -> In b (solve_nqueens n n []).
Proof.
  revert b.
  induction n as [|n IH]; intros b Hlen Hvalid.
  - destruct b; inversion Hlen. simpl. left. reflexivity.
  - assert (Hn : n = length (tl b)) by (destruct b; simpl in *; lia).
    destruct b as [|col rest]; inversion Hlen.
    simpl in Hvalid. destruct Hvalid as [Hsafe Hvalid_rest].
    simpl.
    apply in_flat_map. exists col.
    rewrite safe_partial_correct in Hsafe. rewrite Hsafe.
    left.
    apply IH.
    + simpl in Hn. assumption.
    + assumption.
Qed.

(* Now we can prove the main theorem *)

Theorem methods_equivalent n :
  Permutation (all_valid_boards n) (n_queens_fast n).
Proof.
  unfold all_valid_boards, n_queens_fast.
  apply Permutation_filter.
  - apply perms_range_permutation.
  - intros b. rewrite valid_equiv. reflexivity.
Qed.

(* Additional helper lemma showing perms produces permutations *)
Lemma perms_range_permutation n :
  Forall (fun b => Permutation (range n) b) (perms (range n)).
Proof.
  induction n as [|n IH]; simpl.
  - constructor. constructor.
  - rewrite range_S. simpl.
    apply Forall_concat. apply Forall_map.
    intros l Hl. apply Forall_forall in IH.
    apply IH in Hl.
    apply insert_all_permutation; auto.
Qed.

(* Helper lemma about insert_all preserving permutations *)
Lemma insert_all_permutation x l :
  Forall (fun l' => Permutation (x :: l) l') (insert_all x l).
Proof.
  induction l as [|y ys IH]; simpl.
  - constructor. constructor.
  - constructor.
    + constructor. apply Permutation_refl.
    + apply Forall_map. intros zs Hzs.
      apply Forall_forall in IH. apply IH in Hzs.
      constructor. assumption.
Qed.






(*
The validb_spec lemma proves the equivalence between the boolean and propositional versions of board validation.
It states that for any board b, validb b = true if and only if valid b.

This is a crucial lemma that connects the computational and logical aspects of the verification.
*)

Lemma safeb_spec : forall col rest row,
  safeb col rest row = true <-> safe col rest row.
Proof.
  induction rest as [|x xs IH]; intros row.
  - (* Base case: empty rest *)
    simpl. split; auto.
  - (* Inductive case: x :: xs *)
    simpl. 
    (* First examine the column equality test *)
    case_eq (col =? x); intro Heq.
    + (* Case where col = x is true *)
      rewrite Nat.eqb_eq in Heq. subst x.
      split.
      * discriminate. (* false = true is impossible *)
      * intros [Hneq _]. now contradict Hneq.
    + (* Case where col = x is false *)
      rewrite Nat.eqb_neq in Heq.
      (* Now examine the diagonal test *)
      case_eq (abs col x =? row); intro Hdiag.
      * (* Diagonal test is true *)
        split.
        -- discriminate. (* false = true is impossible *)
        -- intros [_ [Habs _]]. rewrite Nat.eqb_eq in Hdiag.
           now contradict Habs.
      * (* Diagonal test is false *)
        rewrite Nat.eqb_neq in Hdiag.
        rewrite IH with (row := S row).
        split.
        -- intros Hsafe. repeat split; auto.
        -- intros [H1 [H2 H3]]. auto.
Qed.

Lemma validb_spec : forall b, validb b = true <-> valid b.
Proof.
  induction b as [|x xs IH].
  - (* Base case: empty board *)
    simpl. split; auto.
  - (* Inductive case: x :: xs *)
    simpl. rewrite Bool.andb_true_iff.
    rewrite IH. split.
    + intros [Hsafe Hvalid].
      split.
      * apply safeb_spec. apply Hsafe.
      * apply Hvalid.
    + intros [Hsafe Hvalid].
      split.
      * apply safeb_spec. apply Hsafe.
      * apply Hvalid.
Qed.

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


(* Lemma solve_nqueens_correct : forall n k partial b,
  In b (solve_nqueens n k partial) -> 
  valid (b ++ partial) /\ length b = k.
Proof.
  intros n k partial b.
  generalize dependent partial.
  generalize dependent b.
  induction k as [|k' IH]; intros b partial Hb.
  - (* Base case: k = 0 *)
    simpl in Hb. destruct Hb as [Hb | []]. 
    subst. split; simpl; auto.
    + rewrite app_nil_r. reflexivity.
    + apply valid_nil. (* If you have this lemma, or just `simpl; auto` *)
  - (* Inductive case: k = S k' *)
    simpl in Hb.
    apply in_flat_map in Hb. destruct Hb as [col [Hcol Hb]].
    destruct (safe_partial col partial 1) eqn:Hsafe.
    + (* Safe case *)
      apply IH in Hb as [Hval Hlen].
      split.
      * simpl. rewrite <- app_comm_cons.
        apply valid_cons; auto.
        -- apply safeb_spec. assumption.
        -- assumption.
      * simpl. rewrite Hlen. reflexivity.
    + (* Unsafe case - contradiction *)
      discriminate.
Qed.

(* Then derive the original theorem as a corollary *)
Lemma n_queens_fast_correct : forall n b,
  In b (n_queens_fast n) -> valid b /\ length b = n.
Proof.
  intros n b H.
  unfold n_queens_fast in H.
  apply solve_nqueens_correct with (partial := []) in H.
  simpl in H. rewrite app_nil_r in H.
  exact H.
Qed. *)





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
