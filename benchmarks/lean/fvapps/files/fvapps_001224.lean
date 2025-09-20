-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_kth_word (N M K : Nat) (P : List (List Nat)) : String := sorry

theorem minimal_case (N : Nat) (h : 1 ≤ N) (h' : N ≤ 3) : 
  let result := find_kth_word N 1 1 [[1]]
  String.length result = 1 ∧ result = "a" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem edge_cases (N M : Nat) (hN : 2 ≤ N) (hN' : N ≤ 3) (hM : 2 ≤ M) (hM' : M ≤ 3) :
  let result := find_kth_word N M N (List.replicate M (List.replicate N 1))
  String.length result = M ∧ 
  ∀ c ∈ result.data, 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'a'.toNat + N - 1 := sorry

theorem given_cases : 
  find_kth_word 2 5 17 [[7,9], [13,18], [10,12], [4,18], [3,9]] = "aaaba" ∧
  find_kth_word 1 1 1 [[5]] = "a" := sorry
-- </vc-theorems>