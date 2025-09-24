-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Nat.toString (n : Nat) : String :=
  sorry

def is_even (n : Nat) : Bool :=
  sorry

def List.sort {α : Type} [Ord α] (as : List α) : List α :=
  sorry

def even_digit_squares (start : Nat) (stop : Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_even_matches_digit_check (x : Nat) :
  is_even x = (Nat.toString x |>.data |>.all (fun d => (Char.toNat d - 48) % 2 = 0)) :=
sorry

theorem even_digit_squares_properties {a b : Nat}
  (h : a ≤ 1000000 ∧ b ≤ 1000000) :
  let start := min a b
  let stop := max a b
  let result := even_digit_squares start stop
  (∀ x ∈ result, x ≥ start ∧ x ≤ stop) ∧
  (∀ x ∈ result, is_even x = true) ∧
  (∀ x ∈ result, ∃ y:Nat, y * y = x) ∧
  (result = List.sort result) :=
sorry

theorem single_point_range {x : Nat} (h : x ≤ 1000000) :
  let result := even_digit_squares x x
  result ≠ [] →
  (result.length = 1 ∧
   result.head! = x ∧
   is_even x = true ∧
   ∃ y:Nat, y * y = x) :=
sorry
-- </vc-theorems>