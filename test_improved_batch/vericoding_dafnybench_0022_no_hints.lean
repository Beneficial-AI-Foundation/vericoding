/-
  Port of vericoding_dafnybench_0022_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function length<T>(l: List<T>): nat
  match l case Nil => 0 case Cons(_, t) => 1 + length(t)

function at<T>(l: List<T>, i: nat): T
  sorry  -- TODO: implement complex function body


  (h_0 : a.size ≥ 0)
  : length(l) == a.size ∧ ∀ i : Int, 0 ≤ i < length(l) → at(l, i) == a[i]! ∧ ∀ x :: mem(l, x) → ∃ i: Int :: 0 ≤ i < length(l) ∧ a[i]! == x
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks