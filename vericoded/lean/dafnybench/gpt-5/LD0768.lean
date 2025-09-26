import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
namespace VC
@[simp] theorem if_same {α} (c : Prop) [Decidable c] (x : α) : (if c then x else x) = x := by
  by_cases c <;> simp [*]
end VC
-- </vc-helpers>

-- <vc-definitions>
def FindMedian (a b : Array Int) : Int :=
if a.size % 2 = 0 then (a[a.size / 2 - 1]! + b[0]!) / 2 else a[a.size / 2]!
-- </vc-definitions>

-- <vc-theorems>
theorem FindMedian_spec (a b : Array Int) :
a.size = b.size ∧
a.size > 0 ∧
(∀ i, 0 ≤ i ∧ i < a.size - 1 → a[i]! ≤ a[i + 1]!) ∧
(∀ i, 0 ≤ i ∧ i < b.size - 1 → b[i]! ≤ b[i + 1]!) →
FindMedian a b =
if a.size % 2 = 0
then (a[a.size / 2 - 1]! + b[0]!) / 2
else a[a.size / 2]! :=
by intro _; rfl
-- </vc-theorems>
