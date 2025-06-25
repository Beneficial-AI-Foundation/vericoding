// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn palindromic(s: String, i: int, j: int)
  requires 0 <= i <= j <= |s|
{
  j - i < 2 || (s[i] == s[j-1] && palindromic(s, i+1, j-1))
}


// A "common sense" about palindromes: // ATOM 

// A "common sense" about palindromes:
lemma lemma_palindromic_contains(s: string, lo: int, hi: int, lo': int, hi': int)
  requires 0 <= lo <= lo' <= hi' <= hi <= |s|
  requires lo + hi == lo' + hi'
  requires palindromic(s, lo, hi)
  ensures palindromic(s, lo', hi') -> bool {
    if lo < lo' {
    lemma_palindromic_contains(s, lo + 1, hi - 1, lo', hi');
}

fn expand_from_center(s: String, i0: int, j0: int) -> lo: int, hi: int
    requires 0 <= i0 <= j0 <= s.len(),
             palindromic(s, i0, j0)
    ensures 0 <= lo <= hi <= s.len() and palindromic(s, lo, hi),
            forall|i: int, j  0 <= i <= j <= .len()s| and palindromic(s: int, i: int, j)  // Among all palindromes
    and i + j == i0 + j0                                             // sharing the same center: int, : int| j - i <= hi - lo                                             // `s[lo..hi]` is longest.
{
}

}