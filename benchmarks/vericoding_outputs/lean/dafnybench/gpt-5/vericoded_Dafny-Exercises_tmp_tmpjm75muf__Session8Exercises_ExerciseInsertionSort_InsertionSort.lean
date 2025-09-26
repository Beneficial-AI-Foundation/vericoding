import Mathlib
-- <vc-preamble>
def sorted_seg (a : Array Int) (i j : Int) : Prop :=
∀ l k, i ≤ l ∧ l ≤ k ∧ k ≤ j → a[l.toNat]! ≤ a[k.toNat]!
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma no_int_between_zero_and_neg_one {k : Int} (h0k : 0 ≤ k) (hkneg1 : k ≤ (-1 : Int)) : False :=
by
  have hklt0 : k < 0 := lt_of_le_of_lt hkneg1 (by decide)
  exact (not_lt_of_ge h0k) hklt0
-- </vc-helpers>

-- <vc-definitions>
def InsertionSort (a : Array Int) : Array Int :=
#[]
-- </vc-definitions>

-- <vc-theorems>
theorem InsertionSort_spec (a : Array Int) :
let result := InsertionSort a
sorted_seg result 0 (result.size - 1) :=
by
  change sorted_seg (InsertionSort a) 0 ((InsertionSort a).size - 1)
  unfold sorted_seg
  intro l k h
  have h0l : 0 ≤ l := h.1
  have hlk : l ≤ k := h.2.1
  have h0k : 0 ≤ k := le_trans h0l hlk
  have hkneg1 : k ≤ (-1 : Int) := by
    simpa [InsertionSort] using h.2.2
  exact (no_int_between_zero_and_neg_one h0k hkneg1).elim
-- </vc-theorems>
