-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_permutations (input: String) (k: Nat) : String := sorry 

theorem permutation_length {s: String} {k: Nat} {h: k ≤ String.length s}:
  let perms := get_permutations s k
  ∀ perm ∈ perms.splitOn "\n", String.length perm = k := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem permutation_chars {s: String} {k: Nat} {h: k ≤ String.length s}:
  let perms := get_permutations s k
  let s_chars := s.toList
  ∀ perm ∈ perms.splitOn "\n", ∀ c ∈ perm.toList, c ∈ s_chars := sorry

theorem permutation_sorted {s: String} {k: Nat} {h: k ≤ String.length s}:
  let perms := get_permutations s k
  let perm_list := perms.splitOn "\n"
  ∀ i j: Nat, i < j → j < perm_list.length → 
    perm_list.get ⟨i, by sorry⟩ ≤ perm_list.get ⟨j, by sorry⟩ := sorry

theorem single_char_permutation {s: String} {h: String.length s = 1}:
  get_permutations s 1 = s := sorry
-- </vc-theorems>