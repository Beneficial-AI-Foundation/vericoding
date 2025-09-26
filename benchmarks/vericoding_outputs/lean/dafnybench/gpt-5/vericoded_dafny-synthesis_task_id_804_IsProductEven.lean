import Mathlib
-- <vc-preamble>
def IsEven (n : Int) : Bool :=
n % 2 = 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def AnyEven (a : Array Int) : Prop :=
  ∃ i : Nat, i < a.size ∧ IsEven (a[i]!)

-- </vc-helpers>

-- <vc-definitions>
def IsProductEven (a : Array Int) : Bool :=
decide (∃ i : Nat, i < a.size ∧ IsEven (a[i]!))
-- </vc-definitions>

-- <vc-theorems>
theorem IsProductEven_spec (a : Array Int) :
IsProductEven a ↔ ∃ i, 0 ≤ i ∧ i < a.size ∧ IsEven (a[i]!) :=
by
  constructor
  · intro h
    have hP : ∃ i : Nat, i < a.size ∧ IsEven (a[i]!) := by
      by_contra hnot
      -- Under this assumption, IsProductEven a is False, contradiction
      have : False := by
        simpa [IsProductEven, hnot] using h
      exact this.elim
    rcases hP with ⟨i, hi, hE⟩
    exact ⟨i, Nat.zero_le i, hi, hE⟩
  · intro h
    rcases h with ⟨i, _, hi, hE⟩
    have hP : ∃ i : Nat, i < a.size ∧ IsEven (a[i]!) := ⟨i, hi, hE⟩
    have : IsProductEven a = true := by
      simpa [IsProductEven, hP]
    simpa using this
-- </vc-theorems>
