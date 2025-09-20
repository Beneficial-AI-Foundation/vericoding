-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getSpecialValue : Nat → Nat :=
  sorry

def countNumbersWithSpecialValue : List (Nat × Nat × Nat) → List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem special_value_counts_correct {l r k : Nat} (h1 : l > 0) (h2 : r > l) (h3 : k > 0) (h4 : k ≤ 9) :
  let count := (countNumbersWithSpecialValue [(l,r,k)]).head!;
  count = ((List.range (r-l+1)).filter (fun x => getSpecialValue (x + l) = k)).length := by
  sorry

theorem result_list_length_matches_queries {queries : List (Nat × Nat × Nat)} (h : queries.length > 0) :
  (countNumbersWithSpecialValue queries).length = queries.length := by
  sorry

theorem results_are_nonnegative {queries : List (Nat × Nat × Nat)} (h : queries.length > 0) :
  List.all (countNumbersWithSpecialValue queries) (fun x => x ≥ 0) := by
  sorry
-- </vc-theorems>