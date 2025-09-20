-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_balanced_substrings (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_bounds (s : String) : 
  s.all (fun c => c = '4' || c = '7') → 
  let n := s.length
  let total := n * (n + 1) / 2
  0 ≤ count_balanced_substrings s ∧ count_balanced_substrings s ≤ total :=
  sorry

theorem all_fours (s : String) :
  s.all (fun c => c = '4') →
  let n := s.length
  count_balanced_substrings s = n * (n + 1) / 2 :=
  sorry

theorem single_char_substrings (s : String) :
  s.length > 0 →
  s.all (fun c => c = '4' || c = '7') →
  count_balanced_substrings s ≥ (s.toList.filter (· = '4')).length :=
  sorry

theorem empty_and_single (s : String) :
  s.all (fun c => c = '4' || c = '7') →
  (s.length = 0 → count_balanced_substrings s = 0) ∧
  (s.length = 1 → count_balanced_substrings s = if s = "4" then 1 else 0) :=
  sorry

theorem consecutive_sevens_reduce (s : String) :
  s.all (fun c => c = '4' || c = '7') →
  let n := s.length
  let total := n * (n + 1) / 2
  let consecutive_reduction := 
    s.toList.foldl
      (fun (acc, consec) c => 
        if c = '7' 
        then (acc + consec + 1, consec + 1)
        else (acc, 0))
      (0, 0)
  count_balanced_substrings s = total - consecutive_reduction.1 :=
  sorry
-- </vc-theorems>