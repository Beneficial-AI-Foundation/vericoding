/-
  Port of vericoding_dafnybench_0038_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def convert_map_key (inputs : map<nat) bool> (f : nat->nat) : map<nat :=
  sorry  -- TODO: implement function body

theorem convert_map_key_spec (inputs : map<nat) bool> (f : nat->nat) (r : map<nat) :=
  (h_0 : ∀ n1: nat, n2: nat :: n1 ≠ n2 → f(n1) ≠ f(n2))
  : ∀ k :: k in inputs <→ f(k) in r ∧ ∀ k :: k in inputs → r[f(k)] == inputs[k]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks