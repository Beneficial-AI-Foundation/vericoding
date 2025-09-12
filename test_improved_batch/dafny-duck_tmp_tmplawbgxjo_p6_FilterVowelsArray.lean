/-
  Port of dafny-duck_tmp_tmplawbgxjo_p6_FilterVowelsArray.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FilterVowels (xs : seq<char>) : seq :=
  sorry  -- TODO: implement complex function body

def FilterVowelsArray (xs : Array Char) : Array Char :=
  sorry  -- TODO: implement function body

theorem FilterVowelsArray_spec (xs : Array Char) (ys : Array Char) :=
  : fresh(ys) ∧ FilterVowels(xs[..]) == ys[..]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks