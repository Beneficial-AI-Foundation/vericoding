-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_money_stolen (n : Nat) (money : List Int) (k : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_money_stolen_nonnegative 
  {n : Nat} {money : List Int} {k : Nat}
  (h1 : k > 0)
  (h2 : k ≤ n)
  (h3 : money.length = n)
  (h4 : ∀ x ∈ money, x ≥ 0) :
  max_money_stolen n money k ≥ 0 :=
  sorry

theorem max_money_stolen_upper_bound
  {n : Nat} {money : List Int} {k : Nat}
  (h1 : k > 0)
  (h2 : k ≤ n)
  (h3 : money.length = n)
  (h4 : ∃ maxVal : Int, ∀ x ∈ money, x ≤ maxVal) :
  let maxVal := Classical.choose h4
  max_money_stolen n money k ≤ k * maxVal :=
  sorry

theorem max_money_stolen_fails_k_zero
  {n : Nat} {money : List Int}
  (h : money.length = n) :
  ¬∃ x, max_money_stolen n money 0 = x :=
  sorry

theorem max_money_stolen_fails_k_negative
  {n : Nat} {money : List Int} {k : Int}
  (h1 : money.length = n)
  (h2 : k < 0) :
  ¬∃ x, max_money_stolen n money (Int.toNat k) = x :=
  sorry
-- </vc-theorems>