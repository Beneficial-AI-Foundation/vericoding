-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def artificial_rain (garden: List Nat) : Nat := sorry

theorem artificial_rain_length_invariant {garden: List Nat} (h: garden ≠ []) :
  1 ≤ artificial_rain garden ∧ artificial_rain garden ≤ garden.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem artificial_rain_identical_values {garden: List Nat} (h: garden.length ≥ 2) 
  (h2: ∀ (i j: Nat) (hi: i < garden.length) (hj: j < garden.length), garden.get ⟨i, hi⟩ = garden.get ⟨j, hj⟩) :
  artificial_rain garden = garden.length := sorry

theorem artificial_rain_single_peak_singleton {garden: List Nat} (h: garden.length = 1) :
  artificial_rain garden = 1 := sorry

theorem artificial_rain_single_peak {garden: List Nat} (h: garden.length > 1)
  (peak_idx: Nat) (h2: peak_idx < garden.length)
  (h3: ∀ (i: Nat) (hi: i < garden.length) (hip: i < peak_idx) (hi1: i + 1 < garden.length), 
    garden.get ⟨i, hi⟩ ≤ garden.get ⟨i + 1, hi1⟩)
  (h4: ∀ (i: Nat) (hi: i < garden.length) (hip: peak_idx ≤ i) (hi1: i + 1 < garden.length), 
    garden.get ⟨i, hi⟩ ≥ garden.get ⟨i + 1, hi1⟩) :
  artificial_rain garden ≥ peak_idx + 1 := sorry

theorem artificial_rain_monotonic_increasing {garden: List Nat} (h: garden.length ≥ 2)
  (h2: ∀ (i: Nat) (hi: i < garden.length) (hi1: i + 1 < garden.length), 
    garden.get ⟨i, hi⟩ ≤ garden.get ⟨i + 1, hi1⟩) :
  artificial_rain garden = garden.length := sorry

theorem artificial_rain_monotonic_decreasing {garden: List Nat} (h: garden.length ≥ 2)
  (h2: ∀ (i: Nat) (hi: i < garden.length) (hi1: i + 1 < garden.length), 
    garden.get ⟨i, hi⟩ ≥ garden.get ⟨i + 1, hi1⟩) :
  artificial_rain garden = garden.length := sorry
-- </vc-theorems>