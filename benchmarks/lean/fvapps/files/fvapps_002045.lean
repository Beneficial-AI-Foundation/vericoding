-- <vc-preamble>
def isSorted (l : List Nat) : Prop :=
match l with
| [] => True
| x::xs => match xs with
  | [] => True
  | y::_ => x ≤ y ∧ isSorted xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_max_beauty (n k : Nat) (arr : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_max_beauty_properties
  (n k : Nat) (arr : List Nat)
  (h₁ : n > 0)
  (h₂ : n ≤ 100)
  (h₃ : k ≤ 100)
  (h₄ : arr.length > 0)
  (h₅ : arr.length ≤ 100)
  (h₆ : ∀ x ∈ arr, x > 0 ∧ x ≤ 1000)
  (h₇ : isSorted arr)
  (h₈ : arr.Nodup) :
  let result := get_max_beauty n k arr

  result > 0 ∧

  result ≤ arr.head! ∧

  (∀ x ∈ arr, x % result ≤ k) ∧

  ∀ i ∈ List.range 10,
    i < arr.head! - result + 1 →
    ∃ x ∈ arr, x % (result + i + 1) > k :=
sorry

theorem same_k_different_n
  (arr : List Nat)
  (h₁ : arr.length ≥ 2)
  (h₂ : ∀ x ∈ arr, x > 0 ∧ x ≤ 1000)
  (h₃ : isSorted arr)
  (h₄ : arr.Nodup) :
  get_max_beauty arr.length 1 arr = get_max_beauty (arr.length - 1) 1 arr :=
sorry

theorem k_zero_case
  (n : Nat)
  (arr : List Nat)
  (h₁ : n > 0 ∧ n ≤ 10)
  (h₂ : arr.length > 0 ∧ arr.length ≤ 10)
  (h₃ : ∀ x ∈ arr, x > 0 ∧ x ≤ 1000) :
  let result := get_max_beauty n 0 arr
  ∀ x ∈ arr, x % result = 0 :=
sorry
-- </vc-theorems>