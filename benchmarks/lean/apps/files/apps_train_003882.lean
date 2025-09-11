-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_a (lst : List Int) (n : Int) : Int := sorry

def reverse (lst : List Int) : List Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_a_first_four {lst : List Int} (n : Int)
  (h1 : lst.length = 4)
  (h2 : 0 ≤ n)
  (h3 : n < 4) :
  find_a lst n = lst.get ⟨n.toNat, sorry⟩ := sorry

theorem find_a_recurrence {lst : List Int} (n : Int)
  (h1 : lst.length = 4)
  (h2 : n ≥ 4) :
  find_a lst n = 
    6 * find_a lst (n-1) - 
    10 * find_a lst (n-2) + 
    6 * find_a lst (n-3) - 
    find_a lst (n-4) := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_a [1, 2, 3, 4] 2

/-
info: 200
-/
-- #guard_msgs in
-- #eval find_a [38, 200, -18, 45] 1

/-
info: 20
-/
-- #guard_msgs in
-- #eval find_a [1, 0, 0, 1] 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible