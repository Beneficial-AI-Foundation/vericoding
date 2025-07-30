/-
  Add One Function
  
  Ported from Dafny specification: cs357_tmp_tmpn4fsvwzs_lab7_question2_spec.dfy
  
  This function returns the input plus one.
-/

import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns x + 1 -/
def addOne (x : Int) : Id Int := 
  sorry

/-- Specification: addOne returns x + 1 -/
theorem addOne_spec (x : Int) :
  ⦃⌜True⌝⦄ 
  addOne x
  ⦃⇓result => ⌜result = x + 1⌝⦄ := by
  mvcgen [addOne]
  sorry