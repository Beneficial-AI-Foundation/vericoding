/-
  Port of llm-verified-eval_tmp_tmpd2deqn_i_dafny_161_Reverse.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsLetter (c : Char) : Bool :=
  (c ≥ 'a' ∧ c ≤ 'z') ∨ (c ≥ 'A' ∧ c ≤ 'Z')

def NoLetters (s : String) (n : Nat) : Bool :=
  ∀ c :: 0 ≤ c < n → !IsLetter(s[c]!)

def ToggleCase (c : Char) : Char :=
  if c ≥ 'a' ∧ c ≤ 'z' then (c - 'a' + 'A') else if c ≥ 'A' ∧ c ≤ 'Z' then (c - 'A' + 'a') else c

def isReverse (s : String) (s_prime : String) : Bool :=
  sorry  -- TODO: implement function body

def Reverse (original : seq<char>) : seq<char> :=
  sorry  -- TODO: implement function body

theorem Reverse_spec (original : seq<char>) (reversed : seq<char>) :=
  : |reversed| == |original| ∧ ∀ i :: 0 ≤ i < |original| → reversed[i]! == original[|original| - 1 - i]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks