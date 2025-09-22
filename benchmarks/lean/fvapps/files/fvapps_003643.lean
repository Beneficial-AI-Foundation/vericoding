-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse (nums : List Int) : List Int := sorry

theorem reverse_length_preservation {nums : List Int} :
  (List.length (reverse nums)) = (List.length nums) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_nonempty_preservation {nums : List Int} :
  nums ≠ [] → reverse nums ≠ [] := sorry

theorem reverse_last_element_preservation {nums : List Int} (h : nums ≠ []) :
  List.getLast nums h = List.getLast (reverse nums) (reverse_nonempty_preservation h) := sorry
-- </vc-theorems>