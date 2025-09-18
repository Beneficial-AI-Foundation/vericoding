-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_performance (n : Nat) (speeds : List Nat) (efficiencies : List Nat) (k : Nat) : Nat := sorry

def MOD := 1000000007
-- </vc-definitions>

-- <vc-theorems>
theorem max_performance_mod (n : Nat) (speeds : List Nat) (efficiencies : List Nat) (k : Nat) :
  0 ≤ max_performance n speeds efficiencies k ∧ 
  max_performance n speeds efficiencies k < MOD := sorry

theorem max_performance_geq_single_max (n : Nat) (speeds : List Nat) (efficiencies : List Nat) (k : Nat)
  (h1 : speeds.length = n) (h2 : efficiencies.length = n) (h3 : k ≤ n) :
  ∃ maxProd : Nat, 
    maxProd = List.foldr (fun i acc => max acc ((speeds.get! i) * (efficiencies.get! i))) 0 (List.range n) ∧
    max_performance n speeds efficiencies k ≥ maxProd := sorry

theorem max_performance_monotone (n : Nat) (speeds : List Nat) (efficiencies : List Nat) 
  (k : Nat) (h1 : k > 1) (h2 : k ≤ n) :
  max_performance n speeds efficiencies k ≥ 
  max_performance n speeds efficiencies (k-1) := sorry

theorem max_performance_min_case :
  max_performance 1 [1] [1] 1 = 1 := sorry

theorem max_performance_k_one (n : Nat) (speeds : List Nat) (efficiencies : List Nat)
  (h1 : speeds = [2,1,3]) (h2 : efficiencies = [3,2,1]) (h3 : n = 3) :
  max_performance n speeds efficiencies 1 = 6 := sorry
-- </vc-theorems>