-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def startsWith (s : String) (pre : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem starts_with_matches_python (s pre : String) :
  startsWith s pre = String.startsWith s pre :=
  sorry

theorem empty_prefix_true (s : String) :
  startsWith s "" = true :=
  sorry

theorem long_prefix_false (s pre : String) :
  pre.length > s.length → startsWith s pre = false :=
  sorry

theorem self_prefix (s : String) :
  startsWith s s = true :=
  sorry

theorem prefix_matches_slice (s pre : String) :
  startsWith s pre = (if pre.length = 0 then true else s.take pre.length = pre) :=
  sorry
-- </vc-theorems>