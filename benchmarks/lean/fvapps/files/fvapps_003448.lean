-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def primef (n : Nat) : List Nat := sorry

def sflpf_data (val : Nat) (nmax : Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem primef_product_equals_input (n : Nat) (h : n ≥ 2) : 
  (List.foldl (· * ·) 1 (primef n)) = n := sorry

theorem primef_all_prime (n : Nat) (h : n ≥ 2) :
  ∀ f ∈ primef n, ∀ i : Nat, 2 ≤ i → i < f → i ∣ f → i = f := sorry

theorem sflpf_data_bounds (val nmax : Nat) (h1 : val ≥ 2) (h2 : nmax ≥ 4) :
  ∀ n ∈ sflpf_data val nmax, 4 ≤ n ∧ n ≤ nmax := sorry

theorem sflpf_data_sum_property (val nmax : Nat) (h1 : val ≥ 2) (h2 : nmax ≥ 4) :
  ∀ n ∈ sflpf_data val nmax, 
    List.length (primef n) > 1 ∧ 
    List.head! (primef n) + List.getLast! (primef n) = val := sorry
-- </vc-theorems>