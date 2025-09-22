-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findMinWeakness (sequence : List Int) : Int :=
  sorry

-- Non-negative property
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_weakness_nonneg (sequence : List Int) (h : sequence.length ≥ 2) : 
  findMinWeakness sequence ≥ 0 := sorry

-- Scaling property 

theorem find_min_weakness_scaling (sequence : List Int) (h : sequence.length ≥ 2) :
  findMinWeakness (sequence.map (· * 2)) = 2 * findMinWeakness sequence := sorry

-- Symmetry under reversal

theorem find_min_weakness_reverse_invariant (sequence : List Int) (h : sequence.length ≥ 2) :
  findMinWeakness sequence = findMinWeakness sequence.reverse := sorry

-- Invariance under constant shift

theorem find_min_weakness_shift_invariant (sequence : List Int) (offset : Int) 
  (h : sequence.length ≥ 2) :
  findMinWeakness sequence = findMinWeakness (sequence.map (· + offset)) := sorry
-- </vc-theorems>