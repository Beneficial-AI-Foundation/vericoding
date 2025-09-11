-- <vc-preamble>
def build_or_buy (hand : String) : List String := sorry

def ValidResources := "bwsog"
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countChar (s : List Char) (c : Char) : Nat :=
  s.filter (· = c) |>.length
-- </vc-definitions>

-- <vc-theorems>
theorem build_or_buy_returns_list (hand : String) :
  hand.data.all (· ∈ ValidResources.data) →
  build_or_buy hand ≠ [] ∨ build_or_buy hand = [] := by
  sorry

theorem build_or_buy_valid_items (hand : String) (result : List String) :
  hand.data.all (· ∈ ValidResources.data) →
  result = build_or_buy hand →
  result.all (· ∈ ["road", "settlement", "city", "development"]) := by
  sorry

theorem can_build_road (hand : String) :
  hand.data.all (· ∈ ValidResources.data) →
  "road" ∈ build_or_buy hand →
  countChar hand.data 'b' ≥ 1 ∧ countChar hand.data 'w' ≥ 1 := by
  sorry

theorem can_build_settlement (hand : String) :
  hand.data.all (· ∈ ValidResources.data) →
  "settlement" ∈ build_or_buy hand →
  countChar hand.data 'b' ≥ 1 ∧ countChar hand.data 'w' ≥ 1 ∧
  countChar hand.data 's' ≥ 1 ∧ countChar hand.data 'g' ≥ 1 := by
  sorry

theorem can_build_city (hand : String) :
  hand.data.all (· ∈ ValidResources.data) →
  "city" ∈ build_or_buy hand →
  countChar hand.data 'o' ≥ 3 ∧ countChar hand.data 'g' ≥ 2 := by
  sorry

theorem can_build_development (hand : String) :
  hand.data.all (· ∈ ValidResources.data) →
  "development" ∈ build_or_buy hand →
  countChar hand.data 'o' ≥ 1 ∧ countChar hand.data 's' ≥ 1 ∧
  countChar hand.data 'g' ≥ 1 := by
  sorry

theorem empty_hand_empty_result :
  build_or_buy "" = [] := by
  sorry

theorem result_consistency (hand : String) :
  hand.data.all (· ∈ ValidResources.data) →
  build_or_buy hand = build_or_buy hand := by
  sorry

/-
info: ['road']
-/
-- #guard_msgs in
-- #eval build_or_buy "bwoo"

/-
info: []
-/
-- #guard_msgs in
-- #eval build_or_buy ""

/-
info: ['city']
-/
-- #guard_msgs in
-- #eval build_or_buy "ogogoogogo"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded