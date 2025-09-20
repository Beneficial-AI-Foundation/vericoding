-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sel_reverse (arr : List α) (length : Nat) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_preservation {α : Type} (arr : List α) (length : Nat) :
  List.length (sel_reverse arr length) = List.length arr := sorry
-- </vc-theorems>