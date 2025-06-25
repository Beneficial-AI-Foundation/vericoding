use vstd::prelude::*;

verus! {

spec fn palindromic(s: Seq<char>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= s.len()
{
    j - i < 2 || (s[i] == s[j-1] && palindromic(s, i+1, j-1))
}

proof fn lemma_palindromic_contains(s: Seq<char>, lo: int, hi: int, lo_prime: int, hi_prime: int)
    requires 
        0 <= lo <= lo_prime <= hi_prime <= hi <= s.len(),
        lo + hi == lo_prime + hi_prime,
        palindromic(s, lo, hi)
    ensures palindromic(s, lo_prime, hi_prime)
{
    if lo < lo_prime {
        lemma_palindromic_contains(s, lo + 1, hi - 1, lo_prime, hi_prime);
    }
}

pub fn expand_from_center(s: Seq<char>, i0: int, j0: int) -> (lo: int, hi: int)
    requires 
        0 <= i0 <= j0 <= s.len(),
        palindromic(s, i0, j0)
    ensures 
        0 <= lo <= hi <= s.len() && palindromic(s, lo, hi),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) && i + j == i0 + j0 ==> j - i <= hi - lo
{
}

}