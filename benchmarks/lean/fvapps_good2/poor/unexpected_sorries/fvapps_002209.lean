def getSpecialValue : Nat → Nat :=
  fun n => sorry

def countNumbersWithSpecialValue : List (Nat × Nat × Nat) → List Nat :=
  fun queries => sorry

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

-- Apps difficulty: competition
-- Assurance level: unguarded

/--
info: [1, 4, 0, 8]
-/
#guard_msgs in
#eval count_numbers_with_special_value [(22, 73, 9), (45, 64, 6), (47, 55, 7), (2, 62, 4)]

/--
info: [3, 1, 1, 5]
-/
#guard_msgs in
#eval count_numbers_with_special_value [(82, 94, 6), (56, 67, 4), (28, 59, 9), (39, 74, 4)]