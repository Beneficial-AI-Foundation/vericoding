-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def determine_winner (n : Nat) (alice : List Nat) (bob : List Nat) : String := sorry

theorem determine_winner_returns_valid_result (n : Nat) (alice bob : List Nat) :
  n ≥ 2 → List.length alice = n → List.length bob = n →
  determine_winner n alice bob = "Alice" ∨ 
  determine_winner n alice bob = "Bob" ∨
  determine_winner n alice bob = "Draw" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem determine_winner_symmetry (n : Nat) (alice bob : List Nat) :
  n ≥ 2 → List.length alice = n → List.length bob = n →
  (determine_winner n alice bob = "Alice" → determine_winner n bob alice = "Bob") ∧
  (determine_winner n alice bob = "Bob" → determine_winner n bob alice = "Alice") ∧
  (determine_winner n alice bob = "Draw" → determine_winner n bob alice = "Draw") := sorry

theorem determine_winner_translation_invariant (n : Nat) (alice bob : List Nat) (k : Nat) :
  n ≥ 2 → List.length alice = n → List.length bob = n →
  determine_winner n (List.map (· + k) alice) (List.map (· + k) bob) = 
  determine_winner n alice bob := sorry

theorem determine_winner_scale_invariant (n : Nat) (alice bob : List Nat) (k : Nat) :
  k > 0 → n ≥ 2 → List.length alice = n → List.length bob = n →
  determine_winner n (List.map (· * k) alice) (List.map (· * k) bob) = 
  determine_winner n alice bob := sorry

theorem determine_winner_identical_lists (n : Nat) (x : Nat) :
  n ≥ 2 → determine_winner n (List.replicate n x) (List.replicate n x) = "Draw" := sorry
-- </vc-theorems>