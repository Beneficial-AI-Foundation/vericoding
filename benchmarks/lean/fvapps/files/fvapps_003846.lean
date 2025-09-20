-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_factorial (n : Int) : String := sorry

theorem forward_reverse_factorial {n : Nat} (h : 1 ≤ n ∧ n ≤ 10) :
  let factorial := (List.range n).foldl (fun x y => x * (y+1)) 1
  reverse_factorial (Int.ofNat factorial) = s!"{n}!" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nonmatching_numbers_return_none {n : Int} (h : 1 ≤ n ∧ n ≤ 10000) :
  ¬(∃ k : Nat, (List.range k).foldl (fun x y => x * (y+1)) 1 = Int.toNat n) →
  reverse_factorial n = "None" := sorry

theorem nonpositive_returns_none {n : Int} (h : n ≤ 0) :
  reverse_factorial n = "None" := sorry

theorem known_factorials :
  reverse_factorial 1 = "1!" ∧
  reverse_factorial 2 = "2!" ∧
  reverse_factorial 6 = "3!" := sorry
-- </vc-theorems>