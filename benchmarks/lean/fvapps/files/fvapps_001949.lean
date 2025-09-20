-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pow (base : Nat) (exp : Nat) (mod : Nat) : Nat := sorry

def solve_dolls (n : Nat) (m : Nat) (dolls : List Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_dolls_minimal_case (n : Nat) (hn : 0 < n ∧ n ≤ 10):
  solve_dolls n 0 (List.replicate n 0) = [pow 2 n 998244353] := sorry

theorem solve_dolls_output_length (n m : Nat) 
  (hn : 0 < n ∧ n ≤ 10) (hm : m ≤ 4) :
  List.length (solve_dolls n m (List.replicate n 0)) = m + 1 := sorry
-- </vc-theorems>