-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isBalanced (s : String) : Bool :=
sorry

def balancedParens (n : Nat) : List String :=
sorry

def catalan (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem balanced_parens_output_is_balanced (n : Nat) (h : n ≤ 5) :
  ∀ s ∈ balancedParens n, isBalanced s = true :=
sorry

theorem balanced_parens_length (n : Nat) (h : n ≤ 5) :
  ∀ s ∈ balancedParens n, s.length = 2 * n :=
sorry

theorem balanced_parens_unique (n : Nat) (h : n ≤ 5) :
  (balancedParens n).Nodup :=
sorry

theorem balanced_parens_only_parens (n : Nat) (h : n ≤ 5) :
  ∀ s ∈ balancedParens n, ∀ c ∈ s.toList, c = '(' ∨ c = ')' :=
sorry

theorem balanced_parens_catalan (n : Nat) (h : n ≤ 5) :
  (balancedParens n).length = catalan n :=
sorry

theorem balanced_parens_non_negative (n : Int) :
  n ≥ 0 → ∃ (l : List String), l = balancedParens n.toNat :=
sorry
-- </vc-theorems>