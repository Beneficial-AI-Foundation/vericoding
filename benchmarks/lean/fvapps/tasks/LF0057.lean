-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n: Nat) (arr: List Int) : String := sorry

theorem solve_consistency (n: Nat) (arr: List Int) (h: arr.length > 0) :
  solve n arr = "YES" ∨ solve n arr = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_depends_on_first_last (n: Nat) (arr: List Int) (h: arr.length > 0) :
  ∀ arr2: List Int,
  arr2.length = arr.length →
  arr2.head? = arr.head? →
  arr2.getLast? = arr.getLast? →
  solve n arr2 = solve n arr := sorry

theorem solve_condition (n: Nat) (arr: List Int) (h: arr.length > 0) :
  (solve n arr = "YES" ↔ arr.getLast?.get! > arr.head?.get!) := sorry
-- </vc-theorems>