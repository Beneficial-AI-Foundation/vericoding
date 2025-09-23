-- <vc-preamble>
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_permutation (n : Nat) (k : Nat) : String := sorry

theorem permutation_length (n : Nat) (k : Nat) (h1 : n ≥ 1) (h2 : n ≤ 9) 
    (h3 : k ≥ 1) (h4 : k ≤ factorial n) :
  (get_permutation n k).length = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem permutation_digits_valid (n : Nat) (k : Nat) (h1 : n ≥ 1) (h2 : n ≤ 9)
    (h3 : k ≥ 1) (h4 : k ≤ factorial n) :
  ∀ (c : Char), c ∈ (get_permutation n k).data → 
    ∃ d : Nat, d < 10 ∧ d > 0 ∧ c = Char.ofNat (d + 48) := sorry

theorem permutation_unique_chars (n : Nat) (k : Nat) (h1 : n ≥ 1) (h2 : n ≤ 9)
    (h3 : k ≥ 1) (h4 : k ≤ factorial n) :
  ∀ c, (get_permutation n k).data.count c ≤ 1 := sorry

theorem first_permutation (n : Nat) (h1 : n ≥ 1) (h2 : n ≤ 9) :
  get_permutation n 1 = String.mk (List.range n |>.map (fun i => Char.ofNat (i + 49))) := sorry

theorem last_permutation (n : Nat) (h1 : n ≥ 1) (h2 : n ≤ 9) :
  get_permutation n (factorial n) = 
    String.mk (List.range n |>.map (fun i => Char.ofNat (n - i + 48))) := sorry
-- </vc-theorems>