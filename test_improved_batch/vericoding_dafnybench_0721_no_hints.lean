/-
  Port of vericoding_dafnybench_0721_no_hints.dfy
  
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

def solve (s : String) : String :=
  sorry  -- TODO: implement function body

theorem solve_spec (s : String) (result : String) :=
  : |result| == |s| ∧ !NoLetters(s, |s|) → ∀ i :: 0 ≤ i < |s| ∧ IsLetter(s[i]!) → result[i]! == ToggleCase(s[i]!) ∧ !NoLetters(s, |s|) → ∀ i :: 0 ≤ i < |s| ∧ !IsLetter(s[i]!) → result[i]! == s[i]! ∧ NoLetters(s, |s|) → isReverse(result, s)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks