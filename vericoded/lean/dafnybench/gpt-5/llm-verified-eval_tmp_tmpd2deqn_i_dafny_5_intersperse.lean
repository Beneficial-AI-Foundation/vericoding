import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed for this iteration.
-- </vc-helpers>

-- <vc-definitions>
def intersperse (numbers : Array Int) (delimiter : Int) : Array Int :=
let m := numbers.size
if h : m = 0 then
  (#[] : Array Int)
else
  let len := 2 * m - 1
  Array.ofFn (fun (i : Fin len) =>
    if hEven : i.val % 2 = 0 then
      numbers[i.val / 2]!
    else
      delimiter
  )
-- </vc-definitions>

-- <vc-theorems>
theorem intersperse_spec (numbers : Array Int) (delimiter : Int) :
let result := intersperse numbers delimiter
(result.size = if numbers.size > 0 then 2 * numbers.size - 1 else 0) ∧
(∀ i, 0 ≤ i ∧ i < result.size → i % 2 = 0 → result[i]! = numbers[i / 2]!) ∧
(∀ i, 0 ≤ i ∧ i < result.size → i % 2 = 1 → result[i]! = delimiter) :=
by
  classical
  let result := intersperse numbers delimiter
  refine And.intro ?hsize ?rest
  · by_cases h0 : numbers.size = 0
    · have : result.size = 0 := by
        simp [result, intersperse, h0]
      simpa [h0] using this
    · have : result.size = 2 * numbers.size - 1 := by
        simp [result, intersperse, h0]
      have hpos : numbers.size > 0 := Nat.pos_of_ne_zero h0
      simpa [hpos] using this
  · refine And.intro ?even ?odd
    · intro i hi hEven
      have hlt : i < result.size := hi.2
      by_cases h0 : numbers.size = 0
      · have : False := by
          have : i < 0 := by simpa [result, intersperse, h0] using hlt
          exact Nat.not_lt_zero _ this
        exact this.elim
      ·
        have hi' : i < 2 * numbers.size - 1 := by
          simpa [result, intersperse, h0] using hlt
        simp [result, intersperse, h0, hi', hEven]
    · intro i hi hOdd
      have hlt : i < result.size := hi.2
      by_cases h0 : numbers.size = 0
      · have : False := by
          have : i < 0 := by simpa [result, intersperse, h0] using hlt
          exact Nat.not_lt_zero _ this
        exact this.elim
      ·
        have hi' : i < 2 * numbers.size - 1 := by
          simpa [result, intersperse, h0] using hlt
        have hne : ¬ i % 2 = 0 := by
          intro hzero
          have : (1 : Nat) = 0 := Eq.trans (Eq.symm hOdd) hzero
          exact Nat.one_ne_zero this
        simp [result, intersperse, h0, hi', hne]
-- </vc-theorems>
