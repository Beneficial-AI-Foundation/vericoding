-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
import Std
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (lst1: List Int) (lst2: List Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List Int → List Int → String)
-- inputs
(lst1: List Int)
(lst2: List Int) :=
-- spec
let spec (result : String) :=
  lst1 ≠ [] → lst2 ≠ [] →
  let bool_result := ∃ exchange: List (Nat × Nat),
    let lst1_idxs := exchange.map (fun (a, _) => a)
    let lst2_idxs := exchange.map (fun (_, b) => b)
    lst1_idxs.all (fun i => i < lst1.length) ∧
    lst2_idxs.all (fun i => i < lst2.length) ∧
    lst1_idxs.Nodup ∧
    lst2_idxs.Nodup ∧
    ∀ i, i < lst1.length →
      (i ∉ lst1_idxs → Even (lst1[i]!)) ∧
      (i ∈ lst1_idxs →
        -- find the (a, b) in exchange where a = i
        let i_idx := (lst1_idxs.indexesOf i).head!
        Even (lst2[lst2_idxs[i_idx]!]!))
  (bool_result → result = "YES") ∧
  (result = "NO" → ¬ bool_result) ∧
  (result ≠ "YES" ∧ result ≠ "NO" → False)
-- program termination
∃ result,
  implementation lst1 lst2 = result ∧
  spec result

theorem correctness
(lst1: List Int)
(lst2: List Int)
: problem_spec implementation lst1 lst2
:= by
  sorry
-- </vc-theorems>