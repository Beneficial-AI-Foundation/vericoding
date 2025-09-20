-- <vc-preamble>
def List.maximum' (l : List Nat) : Nat := 
  match l with
  | [] => 0
  | x::xs => List.foldl Nat.max x xs

def List.isStrictlyIncreasing (l : List Nat) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! < l[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Nat) (T : Nat) (A : List Nat) : Nat := sorry

theorem output_is_valid_count {N T : Nat} {A : List Nat} 
  (h1 : N = A.length)
  (h2 : T = A.maximum')
  (h3 : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000)
  (h4 : 2 ≤ N ∧ N ≤ 100) :
  0 ≤ solve N T A := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem strictly_increasing_has_one_max_gain {N T : Nat} {A : List Nat}
  (h1 : N = A.length)
  (h2 : T = A.maximum')
  (h3 : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000)
  (h4 : 2 ≤ N ∧ N ≤ 100)
  (h5 : A.isStrictlyIncreasing) :
  solve N T A = 1 := sorry

theorem result_bounded_by_input_size {N T : Nat} {A : List Nat}
  (h1 : N = A.length)
  (h2 : T = A.maximum')
  (h3 : ∀ x ∈ A, 1 ≤ x ∧ x ≤ 1000)
  (h4 : 2 ≤ N ∧ N ≤ 100) :
  solve N T A ≤ N := sorry
-- </vc-theorems>