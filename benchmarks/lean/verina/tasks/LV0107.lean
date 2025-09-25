-- <vc-preamble>
import Std.Data.HashSet

@[reducible, simp]
def findFirstRepeatedChar_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findFirstRepeatedChar (s : String) (h_precond : findFirstRepeatedChar_precond (s)) : Option Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findFirstRepeatedChar_postcond (s : String) (result: Option Char) (h_precond : findFirstRepeatedChar_precond (s)) :=
  let cs := s.toList
  match result with
  | some c =>
    let secondIdx := cs.zipIdx.findIdx (fun (x, i) => x = c && i ≠ cs.idxOf c)
    -- Exists repeated char
    cs.count c ≥ 2 ∧
    -- There is no other repeated char before the found one
    List.Pairwise (· ≠ ·) (cs.take secondIdx)
  | none =>
    -- There is no repeated char
    List.Pairwise (· ≠ ·) cs

theorem findFirstRepeatedChar_spec_satisfied (s: String) (h_precond : findFirstRepeatedChar_precond (s)) :
    findFirstRepeatedChar_postcond (s) (findFirstRepeatedChar (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>