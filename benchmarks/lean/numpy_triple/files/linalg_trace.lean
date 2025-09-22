-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def trace {n : Nat} (x : Vector (Vector Float n) n) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem trace_spec {n : Nat} (x : Vector (Vector Float n) n) :
    ⦃⌜True⌝⦄
    trace x
    ⦃⇓result => ⌜result = (List.range n).foldl (fun acc i => 
      if h : i < n then
        acc + (x.get ⟨i, h⟩).get ⟨i, h⟩
      else acc
    ) 0 ∧ 
    (∀ i : Fin n, (x.get i).get i ≠ 0 → result ≠ 0)⌝⦄ := by
  sorry
-- </vc-theorems>