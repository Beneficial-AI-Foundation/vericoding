import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem llm_helper_nonneg_int_ofNat (n : Nat) : 0 ≤ (n : Int) :=
  Int.ofNat_nonneg n
-- </vc-helpers>

-- <vc-definitions>
def CountLists (lists : Array (Array Int)) : Int :=
lists.size
-- </vc-definitions>

-- <vc-theorems>
theorem CountLists_spec (lists : Array (Array Int)) :
let count := CountLists lists
count ≥ 0 ∧ count = lists.size :=
by
  have h : let count := (lists.size : Int); count ≥ 0 ∧ count = lists.size := by
    let count := (lists.size : Int)
    exact And.intro (Int.ofNat_nonneg _) rfl
  simpa [CountLists] using h
-- </vc-theorems>
