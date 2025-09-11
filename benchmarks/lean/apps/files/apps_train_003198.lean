-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def L (n : Nat) (d : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_matches_input (n d : Nat) (h1 : n ≥ 1) (h2 : n ≤ 1000) (h3 : d ≥ 1) (h4 : d ≤ 10) :
  (L n d).length = d :=
sorry

theorem all_digits_unique (n d : Nat) (h1 : n ≥ 1) (h2 : n ≤ 1000) (h3 : d ≥ 1) (h4 : d ≤ 10) :
  let result := L n d
  let chars := result.data
  List.Nodup chars :=
sorry

theorem digits_in_range (n d : Nat) (h1 : n ≥ 1) (h2 : n ≤ 1000) (h3 : d ≥ 1) (h4 : d ≤ 10) :
  let result := L n d
  ∀ c ∈ result.data, c.isDigit ∧ (c.toNat - '0'.toNat) < d :=
sorry

theorem deterministic (n d : Nat) (h1 : n ≥ 1) (h2 : n ≤ 1000) (h3 : d ≥ 1) (h4 : d ≤ 10) :
  L n d = L n d :=
sorry

/-
info: '0'
-/
-- #guard_msgs in
-- #eval L 1 1

/-
info: '02431'
-/
-- #guard_msgs in
-- #eval L 12 5

/-
info: '1325460'
-/
-- #guard_msgs in
-- #eval L 1000 7
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded