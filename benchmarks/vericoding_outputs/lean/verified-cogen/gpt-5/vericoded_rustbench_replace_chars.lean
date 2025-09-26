import Mathlib
-- <vc-preamble>
@[reducible, simp]
def replaceChars_precond (s : Array Char) (old : Char) (new : Char) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma map_replaceChar_size (s : Array Char) (old new : Char) :
  (s.map (fun c => if c = old then new else c)).size = s.size := by
  simp
-- </vc-helpers>

-- <vc-definitions>
def replaceChars (s : Array Char) (old : Char) (new : Char) (h_precond : replaceChars_precond s old new) : Array Char :=
  s.map (fun c => if c = old then new else c)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def replaceChars_postcond (s : Array Char) (old : Char) (new : Char) (result: Array Char) (h_precond : replaceChars_precond s old new) : Prop :=
  result.size = s.size ∧
  (∀ i, i < result.size → result[i]! = (if s[i]! = old then new else s[i]!))

theorem replaceChars_spec_satisfied (s: Array Char) (old: Char) (new: Char) (h_precond : replaceChars_precond s old new) :
    replaceChars_postcond s old new (replaceChars s old new h_precond) h_precond := by
  classical
unfold replaceChars_postcond
constructor
· simp [replaceChars]
· intro i hi
  have hi' : i < s.size := by simpa [replaceChars] using hi
  simp [replaceChars, hi, hi']
-- </vc-theorems>
