use vstd::prelude::*;

verus! {

/* https://leetcode.com/problems/longest-palindromic-substring/
Given a string s, return the longest palindromic substring in s.

Example 1:
Input: s = "babad"
Output: "bab"
Explanation: "aba" is also a valid answer.
*/


// Specifying the problem: whether `s[i..j]` is palindromic
spec fn palindromic(s: Seq<char>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= s.len()
    decreases j - i
{
    j - i < 2 || (s[i] == s[j-1] && palindromic(s, i+1, j-1))
}

// A "common sense" about palindromes:

// A useful "helper function" that returns the longest palindrome at a given center (i0, j0).
fn expand_from_center(s: Seq<char>, i0: usize, j0: usize) -> (res: (usize, usize))
    requires 
        0 <= i0 <= j0 <= s.len(),
        palindromic(s, i0 as int, j0 as int),
    ensures 
        res.0 <= res.1 <= s.len(),
        palindromic(s, res.0 as int, res.1 as int),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j)  
            && i + j == i0 + j0 ==> j - i <= res.1 - res.0,
{
    assume(false);
    (0, 0)
}


// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.

/* Discussions
1. Dafny is super bad at slicing (esp. nested slicing).
  Do circumvent it whenever possible. It can save you a lot of assertions & lemmas!

  For example, instead of `palindromic(s[i..j])`, use the pattern `palindromic(s, i, j)` instead.
  I didn't realize this (ref: https://github.com/Nangos/dafleet/commit/3302ddd7642240ff2b2f6a8c51e8becd5c9b6437),
  Resulting in a couple of clumsy lemmas.

2. Bonus -- Manacher's algorithm
  Our above solution needs `O(|s|^2)` time in the worst case. Can we improve it? Yes.

  Manacher's algorithm guarantees an `O(|s|)` time.
  To get the intuition, ask yourself: when will it really take `O(|s|^2)` time?
  When there are a lot of "nesting and overlapping" palindromes. like in `abcbcbcba` or even `aaaaaa`.

  Imagine each palindrome as a "mirror". "Large mirrors" reflect "small mirrors".
  Therefore, when we "expand" from some "center", we can "reuse" some information from its "mirrored center".
  For example, we move the "center", from left to right, in the string `aiaOaia...`
  Here, the char `O` is the "large mirror".
  When the current center is the second `i`, it is "mirrored" to the first `i` (which we've calculated for),
  so we know the palindrome centered at the second `i` must have at least a length of 3 (`aia`).
  So we can expand directly from `aia`, instead of expanding from scratch.

  Manacher's algorithm is verified below.
  Also, I will verify that "every loop is entered for only `O(|s|)` times",
  which "indirectly" proves that the entire algorithm runs in `O(|s|)` time.
*/


// A reference implementation of Manacher's algorithm:
// (Ref. https://en.wikipedia.org/wiki/Longest_palindromic_substring#Manacher's_algorithm) for details...


// Below are helper functions and lemmas we used:

// Inserts bogus characters to the original string (e.g. from `abc` to `|a|b|c|`).
// Note that this is neither efficient nor necessary in reality, but just for the ease of understanding.
spec fn insert_bogus_chars(s: Seq<char>, bogus: char) -> (s_prime: Seq<char>)
    decreases s.len()
{
    if s.len() == 0 {
        seq![bogus]
    } else {
        let s_prime_old = insert_bogus_chars(s.subrange(1, s.len() as int), bogus);
        let s_prime_new = seq![bogus].add(seq![s[0]]).add(s_prime_old);
        s_prime_new
    }
}

// Returns (max_index, max_value) of array `a` starting from index `start`.
fn argmax(a: &Vec<i32>, start: usize) -> (res: (usize, i32))
    requires 0 <= start < a.len()
    ensures 
        start <= res.0 < a.len() && a[res.0 as int] == res.1,
        forall|i: int| start <= i < a.len() ==> a[i] <= res.1,
    decreases a.len() - start
{
    if start == a.len() - 1 {
        (start, a[start])
    } else {
        let (i, v) = argmax(a, start + 1);
        if a[start] >= v { (start, a[start]) } else { (i, v) }
    }
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
    inbound_radius(s_prime, c, r)
    && palindromic_radius(s_prime, c, r)
    && (forall|r_prime: int| r_prime > r && inbound_radius(s_prime, c, r_prime) ==> !palindromic_radius(s_prime, c, r_prime))
}

// Basically, just "rephrasing" the `lemma_palindromic_contains`,
// talking about center and radius, instead of interval

// When "expand from center" ends, we've find the max radius:

// The critical insight behind Manacher's algorithm.
//
// Given the longest palindrome centered at `c` has length `r`, consider the interval from `c-r` to `c+r`.
// Consider a pair of centers in the interval: `c1` (left half) and `c2` (right half), equally away from `c`.
// Then, the length of longest palindromes at `c1` and `c2` are related as follows:
//, where:
spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

// Transfering our final result on `s'` to that on `s`:

// The following returns whether `s[lo..hi]` is the longest palindrome s.t. `lo + hi == k`:
spec fn max_interval_for_same_center(s: Seq<char>, k: int, lo: int, hi: int) -> bool {
    0 <= lo <= hi <= s.len()
    && lo + hi == k
    && palindromic(s, lo, hi)
    && (forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) && i + j == k ==> j - i <= hi - lo)
}

// Establishes the "palindromic isomorphism" between `s` and `s'`.

// Implies that whenever `c + r` is odd, the corresponding palindrome can be "lengthened for free"
// because its both ends are the bogus char.

// <vc-helpers>
fn expand_from_center(s: Seq<char>, i0: usize, j0: usize) -> (res: (usize, usize))
    requires 
        0 <= i0 <= j0 <= s.len(),
        palindromic(s, i0 as int, j0 as int),
    ensures 
        res.0 <= res.1 <= s.len(),
        palindromic(s, res.0 as int, res.1 as int),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j)  
            && i + j == i0 + j0 ==> j - i <= res.1 - res.0,
{
    let mut i = i0;
    let mut j = j0;
    while i > 0 && j < s.len() && s[i-1] == s[j]
        invariant 0 <= i <= j <= s.len(),
        invariant i + j == i0 as int + j0 as int,
        invariant palindromic(s, i as int, j as int),
        invariant forall|i2: int, j2: int| 0 <= i2 <= j2 <= s.len() && palindromic(s, i2, j2)  
            && i2 + j2 == i0 as int + j0 as int ==> j2 - i2 <= j - i,
    {
        i = i - 1;
        j = j + 1;
        proof {
            assert(s[i as int] == s[j-1]);
            assert(palindromic(s, i as int, j as int));
        }
    }
    (i, j)
}

proof fn lemma_palindromic_radius(s_prime: Seq<char>, c: int, r: int)
    requires max_radius(s_prime, c, r)
    ensures forall|r_prime: int| 0 <= r_prime <= r ==> palindromic_radius(s_prime, c, r_prime)
{
    assert(forall|r_prime: int| 0 <= r_prime <= r ==> inbound_radius(s_prime, c, r_prime) 
        && palindromic_radius(s_prime, c, r_prime));
}

proof fn lemma_palindromic_contains(s_prime: Seq<char>, c: int, r: int, lo: int, hi: int)
    requires palindromic_radius(s_prime, c, r) && c - r <= lo && hi <= c + r
    ensures palindromic(s_prime, lo, hi)
    decreases hi - lo
{
    if hi - lo < 2 {}
    else {
        let mid = (lo + hi) / 2;
        lemma_palindromic_contains(s_prime, c, r, lo, mid);
        lemma_palindromic_contains(s_prime, c, r, mid, hi);
        assert(s_prime[lo] == s_prime[hi - 1]);
    }
}
// </vc-helpers>

// <vc-spec>
fn longestPalindrome(s: Vec<char>) -> (ans: (Vec<char>, usize, usize))
    ensures 
        0 <= ans.1 <= ans.2 <= s.len(),
        ans.0@ == s@.subrange(ans.1 as int, ans.2 as int),  // `ans` is indeed a substring in `s`
        palindromic(s@, ans.1 as int, ans.2 as int),  // `ans` is palindromic
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s@, i, j) ==> j - i <= ans.2 - ans.1,  // `ans` is longest
// </vc-spec>
// <vc-code>
{
    let len = s.len();
    if len == 0 {
        return (Vec::new(), 0, 0);
    }
    
    let mut start = 0;
    let mut max_len = 1;
    
    let mut i = 0;
    while i < len
        invariant 0 <= i <= len,
        invariant 0 <= start < len,
        invariant 1 <= max_len <= len,
        invariant start + max_len <= len,
        invariant palindromic(s@, start as int, (start + max_len) as int),
    {
        // Odd length palindromes
        let (l1, r1) = expand_from_center(s@, i, i + 1);
        let len1 = r1 - l1;
        
        // Even length palindromes
        let (l2, r2) = expand_from_center(s@, i, i);
        let len2 = r2 - l2;
        
        if len1 > max_len {
            max_len = len1;
            start = l1;
        }
        if len2 > max_len {
            max_len = len2;
            start = l2;
        }
        
        i = i + 1;
    }
    
    let result_vec = s.subrange(start as int, (start + max_len) as int).to_vec();
    (result_vec, start, start + max_len)
}
// </vc-code>

fn main() {}

}