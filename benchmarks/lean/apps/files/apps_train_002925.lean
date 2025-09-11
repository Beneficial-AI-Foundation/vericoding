-- <vc-preamble>
def abs (n : Int) : Int := 
  if n ≥ 0 then n else -n

def list_minimum (lst : List Int) : Int := sorry

def array_center (lst : List Int) : List Int := sorry

def mean (lst : List Int) : Int := sorry

theorem array_center_is_subset {lst : List Int} (h : lst ≠ []) : 
  ∀ x, x ∈ array_center lst → x ∈ lst := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_index_of (lst : List Int) (x : Int) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: [4, 5]
-/
-- #guard_msgs in
-- #eval array_center [8, 3, 4, 5, 2, 8]

/-
info: [1, 2, 1]
-/
-- #guard_msgs in
-- #eval array_center [1, 3, 2, 1]

/-
info: [10, 11, 12, 13, 14]
-/
-- #guard_msgs in
-- #eval array_center [10, 11, 12, 13, 14]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible