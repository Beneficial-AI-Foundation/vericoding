use vstd::prelude::*;

verus! {

// Specifying the problem: whether `s[i..j]` is palindromic
spec fn palindromic(s: Seq<char>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= s.len()
{
    j - i < 2 || (s[i] == s[j-1] && palindromic(s, i+1, j-1))
}

// A "common sense" about palindromes:
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

// A useful "helper function" that returns the longest palindrome at a given center (i0, j0).
pub fn expand_from_center(s: Seq<char>, i0: int, j0: int) -> (lo: int, hi: int)
    requires 
        0 <= i0 <= j0 <= s.len(),
        palindromic(s, i0, j0)
    ensures 
        0 <= lo <= hi <= s.len() && palindromic(s, lo, hi),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) && i + j == i0 + j0 ==> j - i <= hi - lo
{
}

// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.
pub fn longestPalindrome(s: Seq<char>) -> (ans: Seq<char>, lo: int, hi: int)
    ensures 
        0 <= lo <= hi <= s.len() && ans == s.subrange(lo, hi),
        palindromic(s, lo, hi),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) ==> j - i <= hi - lo
{
}

pub fn longestPalindrome_prime(s: Seq<char>) -> (ans: Seq<char>, lo: int, hi: int)
    ensures 
        0 <= lo <= hi <= s.len() && ans == s.subrange(lo, hi),
        palindromic(s, lo, hi),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) ==> j - i <= hi - lo
{
}

spec fn insert_bogus_chars(s: Seq<char>, bogus: char) -> Seq<char>
    ensures |insert_bogus_chars(s, bogus)| == 2 * s.len() + 1,
        forall|i: int| 0 <= i <= s.len() ==> insert_bogus_chars(s, bogus)[i * 2] == bogus,
        forall|i: int| 0 <= i < s.len() ==> insert_bogus_chars(s, bogus)[i * 2 + 1] == s[i]
{
    if s.len() == 0 {
        seq![bogus]
    } else {
        let s_prime_old = insert_bogus_chars(s.subrange(1, s.len() as int), bogus);
        let s_prime_new = seq![bogus, s[0]].add(s_prime_old);
        s_prime_new
    }
}

fn argmax(a: &Vec<i32>, start: usize) -> (usize, i32)
    requires 
        0 <= start < a.len()
    ensures 
        start <= argmax(a, start).0 < a.len() && a[argmax(a, start).0] == argmax(a, start).1,
        forall|i: int| start <= i < a.len() ==> a[i] <= argmax(a, start).1
{
}

// Whether an interval at center `c` with a radius `r` is within the boundary of `s'`.
spec fn inbound_radius(s_prime: Seq<char>, c: int, r: int) -> bool
{
    r >= 0 && 0 <= c-r && c+r < s_prime.len()
}

// Whether `r` is a valid palindromic radius at center `c`.
spec fn palindromic_radius(s_prime: Seq<char>, c: int, r: int) -> bool
    recommends inbound_radius(s_prime, c, r)
{
    palindromic(s_prime, c-r, c+r+1)
}

// Whether `r` is the maximal palindromic radius at center `c`.
spec fn max_radius(s_prime: Seq<char>, c: int, r: int) -> bool
{
    && inbound_radius(s_prime, c, r)
    && palindromic_radius(s_prime, c, r)
    && (forall|r_prime: int| r_prime > r && inbound_radius(s_prime, c, r_prime) ==> !palindromic_radius(s_prime, c, r_prime))
}

// Basically, just "rephrasing" the `lemma_palindromic_contains`,
// talking about center and radius, instead of interval
proof fn lemma_palindromic_radius_contains(s_prime: Seq<char>, c: int, r: int, r_prime: int)
    requires 
        inbound_radius(s_prime, c, r) && palindromic_radius(s_prime, c, r),
        0 <= r_prime <= r
    ensures 
        inbound_radius(s_prime, c, r_prime) && palindromic_radius(s_prime, c, r_prime)
{
    lemma_palindromic_contains(s_prime, c-r, c+r+1, c-r_prime, c+r_prime+1);
}

// When "expand from center" ends, we've find the max radius:
proof fn lemma_end_of_expansion(s_prime: Seq<char>, c: int, r: int)
    requires 
        inbound_radius(s_prime, c, r) && palindromic_radius(s_prime, c, r),
        inbound_radius(s_prime, c, r + 1) ==> s_prime[c - (r + 1)] != s_prime[c + (r + 1)]
    ensures max_radius(s_prime, c, r)
{
}

// The critical insight behind Manacher's algorithm.
proof fn lemma_mirrored_palindrome(s_prime: Seq<char>, c: int, r: int, c1: int, r1: int, c2: int)
    requires 
        max_radius(s_prime, c, r) && max_radius(s_prime, c1, r1),
        c - r <= c1 < c < c2 <= c + r,
        c2 - c == c - c1
    ensures 
        c2 + r1 < c + r ==> max_radius(s_prime, c2, r1),
        c2 + r1 > c + r ==> max_radius(s_prime, c2, c + r - c2),
        c2 + r1 == c + r ==> palindromic_radius(s_prime, c2, c + r - c2)
{
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

// Transfering our final result on `s'` to that on `s`:
proof fn lemma_result_transfer(s: Seq<char>, s_prime: Seq<char>, bogus: char, radii: &Vec<i32>, c: int, r: int, hi: int, lo: int)
    requires 
        s_prime == insert_bogus_chars(s, bogus),
        radii.len() == s_prime.len(),
        forall|i: int| 0 <= i < radii.len() ==> max_radius(s_prime, i, radii[i]),
        (c, r) == argmax(radii, 0),
        lo == (c - r) / 2 && hi == (c + r) / 2
    ensures 
        0 <= lo <= hi <= s.len(),
        palindromic(s, lo, hi),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) ==> j - i <= hi - lo
{
}

// The following returns whether `s[lo..hi]` is the longest palindrome s.t. `lo + hi == k`:
spec fn max_interval_for_same_center(s: Seq<char>, k: int, lo: int, hi: int) -> bool {
    && 0 <= lo <= hi <= s.len()
    && lo + hi == k
    && palindromic(s, lo, hi)
    && (forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) && i + j == k ==> j - i <= hi - lo)
}

// Establishes the "palindromic isomorphism" between `s` and `s'`.
proof fn lemma_palindrome_isomorph(s: Seq<char>, s_prime: Seq<char>, bogus: char, lo: int, hi: int)
    requires 
        s_prime == insert_bogus_chars(s, bogus),
        0 <= lo <= hi <= s.len()
    ensures palindromic(s, lo, hi) <==> palindromic_radius(s_prime, lo + hi, hi - lo)
{
}

// Implies that whenever `c + r` is odd, the corresponding palindrome can be "lengthened for free"
// because its both ends are the bogus char.
proof fn lemma_palindrome_bogus(s: Seq<char>, s_prime: Seq<char>, bogus: char, c: int, r: int)
    requires 
        s_prime == insert_bogus_chars(s, bogus),
        inbound_radius(s_prime, c, r) && palindromic_radius(s_prime, c, r),
        (c + r) % 2 == 1
    ensures 
        inbound_radius(s_prime, c, r + 1) && palindromic_radius(s_prime, c, r + 1)
{
}

}