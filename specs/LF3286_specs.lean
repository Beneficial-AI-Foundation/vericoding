-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def disjunction (operands: List Bool) (exclusive: Bool) : Bool := sorry

theorem disjunction_inclusive_or
  {operands: List Bool}
  (h: operands ≠ [])
  : disjunction operands false = List.any operands id := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem disjunction_exclusive_or
  {operands: List Bool}
  (h: operands ≠ [])
  : disjunction operands true = ((List.countP (· = true) operands).mod 2 = 1) := sorry 

theorem disjunction_empty_error
  : ¬∃ (b: Bool), ∃ (res: Bool), disjunction [] b = res := sorry
-- </vc-theorems>