-- <vc-preamble>
def find_mountain_indices (n : Nat) (perm : List Int) : Answer :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_mountain (perm : List Int) (start_idx : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_mountain_indices_valid_format {n : Nat} {perm : List Int} :
  match find_mountain_indices n perm with
  | Answer.YES indices => indices.length = 3
  | Answer.NO => True := sorry

theorem mountain_indices_are_valid {n : Nat} {perm : List Int} :
  match find_mountain_indices n perm with
  | Answer.YES indices => 
    indices.length = 3 →
    ∀ i j k, indices = [i, j, k] →
    1 ≤ i ∧ i < j ∧ j < k ∧ k ≤ n
  | Answer.NO => True := sorry

theorem mountain_indices_form_mountain {n : Nat} {perm : List Int} :
  match find_mountain_indices n perm with
  | Answer.YES indices =>
    indices.length = 3 →
    ∀ i, indices.head? = some i →
    is_mountain perm (i-1)
  | Answer.NO => True := sorry

theorem no_result_means_no_mountain {n : Nat} {perm : List Int} :
  find_mountain_indices n perm = Answer.NO →
  ∀ i, i < n - 2 →
  ¬is_mountain perm i := sorry

theorem increasing_has_no_mountain {n : Nat} {perm : List Int} (h : n ≥ 3) : 
  perm = List.map Int.ofNat (List.range n) →
  find_mountain_indices n perm = Answer.NO := sorry

theorem decreasing_has_no_mountain {n : Nat} {perm : List Int} (h : n ≥ 3) :
  perm = List.map Int.ofNat (List.range n).reverse →
  find_mountain_indices n perm = Answer.NO := sorry

theorem mountain_indices_are_consecutive {n : Nat} {perm : List Int} :
  match find_mountain_indices n perm with
  | Answer.YES indices =>
    indices.length = 3 →
    ∀ i j k, indices = [i, j, k] →
    j = i + 1 ∧ k = j + 1
  | Answer.NO => True := sorry
-- </vc-theorems>