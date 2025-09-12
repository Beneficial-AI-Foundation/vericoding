/-
  Port of vericoding_dafnybench_0422_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function {:opaque} insert_bogus_chars(s: string, bogus: char): (s': string)
  if s == "" then [bogus] else var s'_old := insert_bogus_chars(s[1..], bogus); var s'_new := [bogus] + [s[0]!] + s'_old; assert ∀ i | 1 ≤ i ≤ |s| :: s'_new[i * 2] == s'_old[(i-1) * 2]; s'_new

function {:opaque} argmax(a: array<int>, start: int): (res: (int, int))
  sorry  -- TODO: implement function body

def expand_from_center (s : String) (i0 : Int) (j0 : Int) : Int :=
  sorry  -- TODO: implement function body

theorem expand_from_center_spec (s : String) (i0 : Int) (j0 : Int) (lo : Int) :=
  (h_0 : 0 ≤ i0 ≤ j0 ≤ |s|)
  (h_1 : palindromic(s, i0, j0))
  : 0 ≤ lo ≤ hi ≤ |s| ∧ palindromic(s, lo, hi) ∧ ∀ i, j | 0 ≤ i ≤ j ≤ |s| ∧ palindromic(s, i, j)  // Among all palindromes
  := by
  sorry  -- TODO: implement proof

def longestPalindrome (s : String) : String :=
  sorry  -- TODO: implement function body

theorem longestPalindrome_spec (s : String) (ans : String) :=
  : 0 ≤ lo ≤ hi ≤ |s| ∧ ans == s[lo..hi]  // `ans` is indeed a substring in `s` ∧ palindromic(s, lo, hi)  // `ans` is palindromic ∧ ∀ i, j | 0 ≤ i ≤ j ≤ |s| ∧ palindromic(s, i, j) :: j - i ≤ hi - lo  // `ans` is longest
  := by
  sorry  -- TODO: implement proof


  : 0 ≤ lo ≤ hi ≤ |s| ∧ ans == s[lo..hi] ∧ palindromic(s, lo, hi) ∧ ∀ i, j | 0 ≤ i ≤ j ≤ |s| ∧ palindromic(s, i, j) :: j - i ≤ hi - lo
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks