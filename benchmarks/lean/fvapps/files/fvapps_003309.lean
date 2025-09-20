-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_last (n m : Nat) : Nat × Nat := sorry

theorem result_format {n m : Nat} (hn : n ≥ 2) (hm : m ≥ 1) :
  let (player, coins) := find_last n m
  player ≥ 1 ∧ player ≤ n ∧ coins ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem m_equals_one {n : Nat} (hn : n ≥ 2) :
  (find_last n 1).1 = n := sorry

theorem coins_increase {n1 n2 m : Nat} (h1 : n1 ≥ 2) (h2 : n2 > n1) (hm : m ≥ 1) :
  (find_last n1 m).2 < (find_last n2 m).2 := sorry
-- </vc-theorems>