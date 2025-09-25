-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_cost_to_match_strings (n : Nat) (s1 s2 : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_cost_nonnegative_and_bounded
  (s1 s2 : String)
  (h1 : s1.length > 0)
  (h2 : s2.length > 0)
  (n : Nat := min s1.length s2.length) :
  let result := min_cost_to_match_strings n (s1.take n) (s2.take n)
  0 ≤ result ∧ result ≤ n :=
sorry

theorem min_cost_identical_strings
  (s : String)
  (h : s.length > 0) :
  min_cost_to_match_strings s.length s s = 0 :=
sorry

theorem min_cost_truncation
  (n : Nat)
  (s1 s2 : String)
  (h : n > 0) :
  let s1_pad := if s1.length < n
                then s1 ++ String.mk (List.replicate (n - s1.length) '1')
                else s1.take n
  let s2_pad := if s2.length < n
                then s2 ++ String.mk (List.replicate (n - s2.length) '1')
                else s2.take n
  let result := min_cost_to_match_strings n s1_pad s2_pad
  0 ≤ result ∧ result ≤ n :=
sorry
-- </vc-theorems>