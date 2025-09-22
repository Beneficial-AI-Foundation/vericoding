-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def trace {rows cols : Nat} (a : Vector (Vector Float cols) rows) (offset : Int) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem trace_spec {rows cols : Nat} (a : Vector (Vector Float cols) rows) (offset : Int) :
    ⦃⌜True⌝⦄
    trace a offset
    ⦃⇓result => ⌜
      -- The result is the sum of all valid diagonal elements with the given offset
      -- For offset ≥ 0: sum a[i][i+offset] for valid i where i+offset < cols
      -- For offset < 0: sum a[i-offset][i] for valid i where i-offset ≥ 0
      (if offset ≥ 0 then
        -- For non-negative offset: sum elements where row index i and column index i+offset are both valid
        ∃ (valid_indices : List (Fin rows × Fin cols)),
          (∀ ij ∈ valid_indices, ij.2.val = ij.1.val + offset.natAbs) ∧
          result = valid_indices.foldl (fun acc ij => acc + (a.get ij.1).get ij.2) 0
      else
        -- For negative offset: sum elements where row index i+|offset| and column index i are both valid
        ∃ (valid_indices : List (Fin rows × Fin cols)),
          (∀ ij ∈ valid_indices, ij.1.val = ij.2.val + offset.natAbs) ∧
          result = valid_indices.foldl (fun acc ij => acc + (a.get ij.1).get ij.2) 0)
    ⌝⦄ := by
  sorry
-- </vc-theorems>