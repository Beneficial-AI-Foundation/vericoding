-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def true_binary (n : Nat) : List Int := sorry

theorem true_binary_starts_with_one {n : Nat} (h : n % 2 = 1) :
  match true_binary n with
  | [] => False 
  | x::xs => x = 1
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem true_binary_elements_are_ones {n : Nat} (h : n % 2 = 1) :
  ∀ x ∈ true_binary n, x = 1 ∨ x = -1 := sorry

theorem true_binary_length {n : Nat} (h : n % 2 = 1) :
  List.length (true_binary n) = Nat.log2 n := sorry
-- </vc-theorems>