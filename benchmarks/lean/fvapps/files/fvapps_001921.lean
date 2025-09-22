-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def determine_winner (n : Nat) (numbers : List Nat) : String := sorry

def gcd (a b : Nat) : Nat := sorry

-- Winner is either Alice or Bob
-- </vc-definitions>

-- <vc-theorems>
theorem determine_winner_valid (n : Nat) (numbers : List Nat) 
    (h1 : n > 0) (h2 : n ≤ 100)
    (h3 : ∀ x ∈ numbers, x > 0 ∧ x ≤ 1000)
    (h4 : ¬numbers.isEmpty) (h5 : numbers.length ≤ 100) :
    determine_winner n numbers = "Alice" ∨ determine_winner n numbers = "Bob" := sorry

-- Winner is determined by GCD calculation 

theorem determine_winner_gcd (n : Nat) (numbers : List Nat)
    (h1 : n > 0) (h2 : n ≤ 100)
    (h3 : ∀ x ∈ numbers, x > 0 ∧ x ≤ 1000)
    (h4 : numbers.length ≥ 2) (h5 : numbers.length ≤ 100) :
    let gcd_result := numbers.foldl gcd numbers.head!
    let max_num := numbers.foldl Nat.max numbers.head!
    let moves := max_num / gcd_result - n
    determine_winner n numbers = (if moves % 2 = 0 then "Bob" else "Alice") := sorry

-- Outcome is valid for all even numbers

theorem determine_winner_even (n : Nat) (numbers : List Nat)
    (h1 : n > 0) (h2 : n ≤ 100)
    (h3 : ∀ x ∈ numbers, x > 0)
    (h4 : ∀ x ∈ numbers, x % 2 = 0)
    (h5 : ¬numbers.isEmpty) (h6 : numbers.length ≤ 100) :
    determine_winner n numbers = "Alice" ∨ determine_winner n numbers = "Bob" := sorry
-- </vc-theorems>