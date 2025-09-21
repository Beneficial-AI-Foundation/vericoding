-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diagonal {rows cols : Nat} (a : Vector (Vector Float cols) rows) (offset : Int := 0) : 
  Id (Vector Float (if offset ≥ 0 then min rows (cols - offset.natAbs) else min (rows - offset.natAbs) cols)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diagonal_spec {rows cols : Nat} (a : Vector (Vector Float cols) rows) (offset : Int := 0) 
    (h_valid : if offset ≥ 0 then offset.natAbs ≤ cols else offset.natAbs ≤ rows) :
    ⦃⌜if offset ≥ 0 then offset.natAbs ≤ cols else offset.natAbs ≤ rows⌝⦄
    diagonal a offset
    ⦃⇓result => ⌜
      -- Result size matches the diagonal size
      result.size = (if offset ≥ 0 then min rows (cols - offset.natAbs) else min (rows - offset.natAbs) cols) ∧
      -- Each element is from the correct diagonal position
      (∀ i : Fin result.size, 
        if offset ≥ 0 then
          -- For non-negative offset: a[i, i+offset]
          result.get i = (a.get ⟨i.val, by sorry⟩).get ⟨i.val + offset.natAbs, by sorry⟩
        else
          -- For negative offset: a[i+|offset|, i]
          result.get i = (a.get ⟨i.val + offset.natAbs, by sorry⟩).get ⟨i.val, by sorry⟩) ∧
      -- Sanity check: result is non-empty when matrix is non-empty and offset is valid
      (rows > 0 ∧ cols > 0 → result.size > 0)
    ⌝⦄ := by
  sorry
-- </vc-theorems>