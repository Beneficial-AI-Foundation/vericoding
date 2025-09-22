-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check {α : Type} [BEq α] (lst : List α) (x : α) : Bool := sorry

theorem check_integers (lst : List Int) (x : Int) :
  check lst x = lst.contains x := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_strings (lst : List String) (x : String) :
  check lst x = lst.contains x := sorry
-- </vc-theorems>