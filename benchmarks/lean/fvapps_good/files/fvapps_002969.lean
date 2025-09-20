-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_repeats (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_repeats_nonnegative (s : String) :
  count_repeats s ≥ 0 :=
  sorry

theorem count_repeats_bounded (s : String) :
  count_repeats s ≤ max 0 (s.length - 1) :=
  sorry

theorem count_repeats_empty :
  count_repeats "" = 0 :=
  sorry

theorem count_repeats_length_after_removal (s : String) (h : s.length > 0) :
  s.length - count_repeats s = (s.foldl (fun acc c => if acc.isEmpty || acc.back ≠ c then acc.push c else acc) "").length :=
  sorry

theorem count_repeats_monotonic_on_duplication (s : String) (h : s.length > 0) :
  let doubled := String.join (s.data.map (fun c => String.mk [c, c]))
  count_repeats doubled ≥ count_repeats s :=
  sorry
-- </vc-theorems>