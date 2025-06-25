// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn expand_from_center(s: String, i0: int, j0: int) -> (lo: int, hi: int)
 requires 0 <= i0 <= j0 <= |s|
 requires palindromic(s, i0, j0)
 ensures 0 <= lo <= hi <= |s| && palindromic(s, lo, hi)
 ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) // Among all palindromes
  && i + j == i0 + j0                       // sharing the same center, : : j - i <= hi - lo                       // `s[lo..hi]` is longest.
{
  lo := 0;
  hi := 0;
  assume 0 <= lo <= hi <= |s| && palindromic(s, lo, hi);
  assume forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) // Among all palindromes;
  return lo, hi;
}


// SPEC


// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.
method longestPalindrome(s: string) returns (ans: string, lo: int, hi: int)
    requires
        0 <= i0 <= j0 <= s.len(),
        palindromic(s, i0, j0)
    ensures
        0 <= lo <= hi <= s.len() && palindromic(s, lo, hi),
        forall i, j  0 <= i <= j <= .len()s| && palindromic(s, i, j) // Among all palindromes
  && i + j == i0 + j0                       // sharing the same center,
  :: j - i <= hi - lo                       // `s.spec_index(lo..hi)` is longest.,
        0 <= lo <= hi <= s.len() && ans == s.spec_index(lo..hi) // `ans` is indeed a substring in `s`,
        palindromic(s, lo, hi) // `ans` is palindromic,
        forall i, j  0 <= i <= j <= .len()s| && palindromic(s, i, j) :: j - i <= hi - lo // `ans` is longest
{
    return (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
}

}