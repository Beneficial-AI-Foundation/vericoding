/-
  Port of vericoding_dafnybench_0773_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sum (s : seq<nat>) : Nat :=
  sorry  -- TODO: implement complex function body

function calcRow(M : array2<int>, x : seq<int>, row: nat, start_index: nat) : (product: int)
  sorry  -- TODO: implement complex function body


  (h_0 : Valid(M, x, y, P, leftOvers))
  (h_1 : ∃ p, (p in P ∧ p.opsLeft > 0))
  (h_2 : sum(leftOvers[..]) > 0)
  := by
  sorry  -- TODO: implement proof

def Run (processes : set<Process>) (M : array2<int>) (x : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem Run_spec (processes : set<Process>) (M : array2<int>) (x : Array Int) (y : Array Int) :=
  (h_0 : |processes| == M.Length0)
  (h_1 : (∀ p, q :: p in processes ∧ q in processes ∧ p ≠ q → p.row ≠  q.row))
  (h_2 : (∀ p, q :: p in processes ∧ q in processes → p ≠ q))
  (h_3 : (∀ p :: p in processes → 0 ≤ p.row < M.Length0))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks