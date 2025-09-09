-- <vc-helpers>
-- </vc-helpers>

def nb_dig (n : Nat) (d : Nat) : Nat :=
  sorry

theorem nb_dig_properties (n : Nat) (d : Nat) (h1 : n ≤ 10000) (h2 : d ≤ 9) :
  nb_dig n d ≥ 0 ∧ 
  nb_dig n d ≤ (n + 1) * (String.length (toString (n * n))) :=
  sorry

theorem nb_dig_zero_digit (n : Nat) (h : n ≤ 1000) :
  let squares := (List.range (n + 1)).map (fun i => i * i)
  let countZeroes := fun num => (toString num).data.filter (fun c => c = '0') |>.length
  let totalZeroes := squares.foldl (fun acc x => acc + countZeroes x) 0
  nb_dig n 0 = totalZeroes :=
  sorry

theorem nb_dig_manual_count (n : Nat) (d : Nat) (h1 : n ≤ 100) (h2 : d ≤ 9) :
  let squares := (List.range (n + 1)).map (fun i => i * i)
  let countDigit := fun num => (toString num).data.filter (· = (toString d).get! 0) |>.length
  let totalCount := squares.foldl (fun acc x => acc + countDigit x) 0
  nb_dig n d = totalCount :=
  sorry

theorem nb_dig_edge_cases :
  nb_dig 0 1 = 0 ∧
  nb_dig 0 0 = 1 :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval nb_dig 10 1

/-
info: 11
-/
-- #guard_msgs in
-- #eval nb_dig 25 1

/-
info: 4700
-/
-- #guard_msgs in
-- #eval nb_dig 5750 0

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible