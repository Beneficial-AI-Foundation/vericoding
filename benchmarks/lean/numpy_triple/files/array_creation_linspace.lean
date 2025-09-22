-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def linspace {num : Nat} (start stop : Float) (h : num > 0) : Id (Vector Float num) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem linspace_spec {num : Nat} (start stop : Float) (h : num > 0) :
    ⦃⌜num > 0⌝⦄
    linspace start stop h
    ⦃⇓result => ⌜
      -- First element is always start
      result.get ⟨0, h⟩ = start ∧

      -- Special case: when num = 1, the single element is start
      (num = 1 → ∀ i : Fin num, result.get i = start) ∧

      -- General case: when num > 1
      (num > 1 → 
        let step := (stop - start) / (num - 1).toFloat
        -- Last element is stop
        (result.get ⟨num - 1, Nat.sub_lt h Nat.zero_lt_one⟩ = stop) ∧
        -- All elements follow the linear formula
        (∀ i : Fin num, result.get i = start + i.val.toFloat * step) ∧
        -- Consecutive elements have constant spacing
        (∀ i j : Fin num, i.val + 1 = j.val → 
          result.get j - result.get i = step)) ∧

      -- Monotonicity property
      ((start < stop) → ∀ i j : Fin num, i < j → result.get i < result.get j) ∧
      ((start > stop) → ∀ i j : Fin num, i < j → result.get i > result.get j) ∧
      ((start = stop) → ∀ i : Fin num, result.get i = start) ∧

      -- Bounds property: all elements lie within the interval
      (∀ i : Fin num, 
        result.get i ≥ min start stop ∧ 
        result.get i ≤ max start stop) ∧

      -- Linear interpolation property: each element can be expressed as a weighted average
      (num > 1 → ∀ i : Fin num,
        let t := i.val.toFloat / (num - 1).toFloat
        result.get i = (1 - t) * start + t * stop) ∧

      -- Reverse symmetry: if we compute linspace(stop, start, num), 
      -- element i equals element (num-1-i) of linspace(start, stop, num)
      (num > 1 → ∀ i : Fin num,
        i.val < num - 1 → 
        let j_val := num - 1 - i.val
        j_val < num → 
        result.get i = stop - (i.val.toFloat * (stop - start) / (num - 1).toFloat))
    ⌝⦄ := by
  sorry
-- </vc-theorems>