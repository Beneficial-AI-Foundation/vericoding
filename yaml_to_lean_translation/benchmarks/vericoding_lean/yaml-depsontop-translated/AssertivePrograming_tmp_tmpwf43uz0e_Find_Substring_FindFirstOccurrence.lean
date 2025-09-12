```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "AssertivePrograming_tmp_tmpwf43uz0e_Find_Substring_FindFirstOccurrence",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: AssertivePrograming_tmp_tmpwf43uz0e_Find_Substring_FindFirstOccurrence",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": []
}
-/

namespace DafnyBenchmarks

/-- Predicate indicating if str2 exists as a substring in str1 -/
def ExistsSubstring (str1 str2 : String) : Prop :=
  ∃ offset : Nat, offset ≤ str1.length ∧ 
    (∃ sub : String, sub = str1.extract offset str1.length ∧ str2.isPrefixOf sub)

/-- Post condition for FindFirstOccurrence -/
def Post (str1 str2 : String) (found : Bool) (i : Nat) : Prop :=
  (found ↔ ExistsSubstring str1 str2) ∧
  (found → i + str2.length ≤ str1.length ∧ 
    (∃ sub : String, sub = str1.extract i str1.length ∧ str2.isPrefixOf sub))

/-- Outer invariant for correctness -/
def Outter_Inv_correctness (str1 str2 : String) (found : Bool) (i : Nat) : Prop :=
  (found → (i + str2.length ≤ str1.length ∧ 
    (∃ sub : String, sub = str1.extract i str1.length ∧ str2.isPrefixOf sub))) ∧
  (¬found ∧ 0 < i ∧ i ≤ str1.length ∧ i ≠ str2.length - 1 → 
    ¬(ExistsSubstring (str1.extract 0 i) str2)) ∧
  (¬found → i ≤ str1.length)

/-- Inner invariant for correctness -/
def Inner_Inv_correctness (str1 str2 : String) (i : Nat) (j : Int) (found : Bool) : Prop :=
  0 ≤ j ∧ j ≤ i ∧
  j < str2.length ∧
  i < str1.length ∧
  ((str1.get i = str2.get j) → 
    (∃ sub : String, sub = str1.extract i str1.length ∧ 
     (∃ sub2 : String, sub2 = str2.extract j str2.length ∧ sub2.isPrefixOf sub))) ∧
  (found → j = 0 ∧ str1.get i = str2.get j)

/-- Inner invariant for termination -/
def Inner_Inv_Termination (str1 str2 : String) (i : Nat) (j : Int) 
                         (old_i old_j : Nat) : Prop :=
  old_j - j = old_i - i

/-- Main method specification -/
def FindFirstOccurrence (str1 str2 : String) : (Bool × Nat) :=
  sorry

/-- Main method specification theorem -/
theorem FindFirstOccurrence_spec (str1 str2 : String) :
  let (found, i) := FindFirstOccurrence str1 str2
  Post str1 str2 found i := sorry

end DafnyBenchmarks
```