-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_odds (low high : Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_odds_correct (low high : Int) (h : high ≥ low) (h2 : high - low < 1000) :
  count_odds low high = ((List.range (Int.toNat (high - low + 1))).filter (fun n => (Int.ofNat n + low) % 2 ≠ 0)).length :=
  sorry

theorem count_odds_single_number (n : Int) :
  count_odds n n = if n % 2 = 0 then 0 else 1 :=
  sorry
-- </vc-theorems>