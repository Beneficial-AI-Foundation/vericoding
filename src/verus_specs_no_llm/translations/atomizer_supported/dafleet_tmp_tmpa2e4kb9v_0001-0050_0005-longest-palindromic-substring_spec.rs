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
spec fn inbound_radius(s': String, c: int, r: int) -> bool {
    r >= 0 and 0 <= c-r and c+r < s'.len()
}
spec fn palindromic_radius(s': String, c: int, r: int)
  requires inbound_radius(s', c, r) -> bool {
    palindromic(s', c-r, c+r+1)
}
spec fn max_radius(s': String, c: int, r: int) -> bool {
    and inbound_radius(s', c, r)
  and palindromic_radius(s', c, r)
  and (forall|r' | r' > r and inbound_radius(s': int, c: int, r'): int| !palindromic_radius(s', c, r'))
}
spec fn max_interval_for_same_center(s: String, k: int, lo: int, hi: int) -> bool {
    and 0 <= lo <= hi <= s.len()
  and lo + hi == k
  and palindromic(s, lo, hi)
  and (forall|i: int, j  0 <= i <= j <= .len()s| and palindromic(s: int, i: int, j) and i + j == k: int| j - i <= hi - lo)
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