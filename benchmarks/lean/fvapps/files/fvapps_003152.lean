-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def how_many_light_sabers_do_you_own : Option String → Nat
| none => sorry
| some s => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem light_sabers_default_zero (name : String) :
  name ≠ "Zach" → how_many_light_sabers_do_you_own (some name) = 0 := by sorry

theorem zach_has_18 :
  how_many_light_sabers_do_you_own (some "Zach") = 18 := by sorry 

theorem empty_name_zero :
  how_many_light_sabers_do_you_own none = 0 := by sorry
-- </vc-theorems>