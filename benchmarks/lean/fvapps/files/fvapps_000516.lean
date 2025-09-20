-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_sequence (n s k m M : Nat) : Option (List Nat) := sorry

def sum : List Nat → Nat 
  | [] => 0
  | h :: t => h + sum t
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_bounds
  {n k m M s : Nat}
  (n_min : n ≥ 3)
  (n_max : n ≤ 20)
  (k_min : k ≥ 1) 
  (k_max : k ≤ 20)
  (m_max : m ≤ 10)
  (M_max : M ≤ 20)
  (s_max : s ≤ 200)
  (m_le_M : m ≤ M)
  (k_space : k ≤ n - 2)
  (s_bounds : n * m ≤ s ∧ s ≤ n * M)
  : ∀ result, find_sequence n s k m M = some result →
    (List.length result = n ∧
     List.all result (fun x => m ≤ x ∧ x ≤ M) = true ∧ 
     sum result = s) := sorry
-- </vc-theorems>