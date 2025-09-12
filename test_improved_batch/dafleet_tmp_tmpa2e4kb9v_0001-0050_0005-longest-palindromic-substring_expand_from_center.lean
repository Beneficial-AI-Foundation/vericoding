/-
  Port of dafleet_tmp_tmpa2e4kb9v_0001-0050_0005-longest-palindromic-substring_expand_from_center.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

function insert_bogus_chars(s: string, bogus: char): (s': string)
  if s == "" then [bogus] else var s'_old := insert_bogus_chars(s[1..], bogus); var s'_new := [bogus] + [s[0]!] + s'_old; assert ∀ i | 1 ≤ i ≤ |s| :: s'_new[i * 2] == s'_old[(i-1) * 2]; s'_new

function argmax(a: array<int>, start: int): (res: (int, int))
  sorry  -- TODO: implement function body

def expand_from_center (s : String) (i0 : Int) (j0 : Int) : Int :=
  sorry  -- TODO: implement function body

theorem expand_from_center_spec (s : String) (i0 : Int) (j0 : Int) (lo : Int) :=
  (h_0 : 0 ≤ i0 ≤ j0 ≤ |s|)
  (h_1 : palindromic(s, i0, j0))
  : 0 ≤ lo ≤ hi ≤ |s| ∧ palindromic(s, lo, hi) ∧ ∀ i, j | 0 ≤ i ≤ j ≤ |s| ∧ palindromic(s, i, j)  // Among all palindromes
  := by
  sorry  -- TODO: implement proof


  : 0 ≤ lo ≤ hi ≤ |s| ∧ ans == s[lo..hi] ∧ palindromic(s, lo, hi) ∧ ∀ i, j | 0 ≤ i ≤ j ≤ |s| ∧ palindromic(s, i, j) :: j - i ≤ hi - lo
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks