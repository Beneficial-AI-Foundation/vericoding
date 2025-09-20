-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_first_player_win (pairs : List (Nat × Nat)) : String := sorry

-- Theorem declarations
-- </vc-definitions>

-- <vc-theorems>
theorem can_first_player_win_outputs (pairs : List (Nat × Nat))
  (h1 : ∀ p ∈ pairs, 1 ≤ p.1 ∧ p.1 ≤ 100 ∧ 1 ≤ p.2 ∧ p.2 ≤ 100)
  (h2 : 1 ≤ pairs.length ∧ pairs.length ≤ 10) :
  can_first_player_win pairs = "YES" ∨ can_first_player_win pairs = "NO" := sorry

theorem can_first_player_win_commutative (pairs : List (Nat × Nat))
  (h1 : ∀ p ∈ pairs, 1 ≤ p.1 ∧ p.1 ≤ 100 ∧ 1 ≤ p.2 ∧ p.2 ≤ 100)
  (h2 : 1 ≤ pairs.length ∧ pairs.length ≤ 10) :
  can_first_player_win pairs = can_first_player_win (pairs.map (fun p => (p.2, p.1))) := sorry

theorem can_first_player_win_bases (pairs : List (Nat × Nat))
  (h1 : ∀ p ∈ pairs, p.1 = 1 ∧ 1 ≤ p.2 ∧ p.2 ≤ 100)
  (h2 : 1 ≤ pairs.length ∧ pairs.length ≤ 10) :
  can_first_player_win pairs = "YES" ∨ can_first_player_win pairs = "NO" := sorry

theorem can_first_player_win_ordering_invariant (pairs permuted : List (Nat × Nat))
  (h1 : ∀ p ∈ pairs, 2 ≤ p.1 ∧ p.1 ≤ 100 ∧ 2 ≤ p.2 ∧ p.2 ≤ 100)
  (h2 : 1 ≤ pairs.length ∧ pairs.length ≤ 10)
  (h3 : ∃ perm : List (Nat × Nat) → List (Nat × Nat), perm pairs = permuted) :
  can_first_player_win pairs = can_first_player_win permuted := sorry
-- </vc-theorems>