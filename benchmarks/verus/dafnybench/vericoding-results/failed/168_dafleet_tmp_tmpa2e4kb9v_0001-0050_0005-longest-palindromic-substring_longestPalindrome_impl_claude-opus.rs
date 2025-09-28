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
// Helper lemma to show that any palindrome must have a center
proof fn lemma_palindrome_has_center(s: Seq<char>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        palindromic(s, i, j),
    ensures
        exists|c1: int, c2: int| 0 <= c1 <= c2 <= s.len() && 
            palindromic(s, c1, c2) && 
            c1 + c2 == i + j &&
            (c2 - c1 == 0 || c2 - c1 == 1),
{
    // Every palindrome has a center that's either a single character or between two characters
    if j - i <= 1 {
        assert(palindromic(s, i, j));
        assert(0 <= i <= j <= s.len());
        assert(i + j == i + j);
        assert(j - i == 0 || j - i == 1);
    } else {
        // For longer palindromes, the center is inside
        assert(palindromic(s, i+1, j-1));
    }
}

// Helper lemma for palindrome expansion
proof fn lemma_palindrome_expand(s: Seq<char>, i: int, j: int)
    requires
        0 < i <= j < s.len(),
        palindromic(s, i, j),
        s[i-1] == s[j],
    ensures
        palindromic(s, i-1, j+1),
{
    // By definition of palindromic
}

// Updated expand_from_center to work with Vec<char>
fn expand_from_center_vec(s: &Vec<char>, i0: usize, j0: usize) -> (res: (usize, usize))
    requires 
        0 <= i0 <= j0 <= s.len(),
        palindromic(s@, i0 as int, j0 as int),
    ensures 
        res.0 <= res.1 <= s.len(),
        palindromic(s@, res.0 as int, res.1 as int),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s@, i, j)  
            && i + j == i0 + j0 ==> j - i <= res.1 - res.0,
{
    let mut left = i0;
    let mut right = j0;
    
    // Expand while we can
    while left > 0 && right < s.len() && s[left - 1] == s[right]
        invariant
            0 <= left <= i0,
            j0 <= right <= s.len(),
            left + right == i0 + j0,
            palindromic(s@, left as int, right as int),
            forall|i: int, j: int| 0 <= i <= j <= s.len() && 
                palindromic(s@, i, j) && 
                i + j == i0 + j0 && 
                (i < left as int || j > right as int) ==> 
                j - i <= right - left,
        decreases left,
    {
        proof {
            lemma_palindrome_expand(s@, left as int, right as int);
        }
        left = left - 1;
        right = right + 1;
    }
    
    // Prove postcondition
    proof {
        // The loop stopped, so we can't expand further
        if left > 0 && right < s.len() {
            assert(s@[(left - 1) as int] != s@[right as int]);
        }
        
        // Any palindrome with the same center sum must be within our bounds
        assert forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s@, i, j) && i + j == i0 + j0
            implies j - i <= right - left by {
            if i < left as int || j > right as int {
                // Already handled by loop invariant
            } else {
                // Must be within [left, right]
                assert(i >= left as int && j <= right as int);
                assert(j - i <= right - left);
            }
        }
    }
    
    (left, right)
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
    if s.len() == 0 {
        return (Vec::<char>::new(), 0, 0);
    }
    
    let mut best_start: usize = 0;
    let mut best_end: usize = 1;
    let mut best_len: usize = 1;
    
    // Try all possible centers
    let mut center: usize = 0;
    
    while center < s.len()
        invariant
            0 <= center <= s.len(),
            0 <= best_start <= best_end <= s.len(),
            best_len == best_end - best_start,
            palindromic(s@, best_start as int, best_end as int),
            // best_len is the maximum among all palindromes centered before 'center'
            forall|i: int, j: int| 0 <= i <= j <= s.len() && 
                palindromic(s@, i, j) && 
                i + j < 2 * center ==> 
                j - i <= best_len,
        decreases s.len() - center,
    {
        // Try odd-length palindrome centered at 'center'
        let (start1, end1) = expand_from_center_vec(&s, center, center + 1);
        if end1 - start1 > best_len {
            best_start = start1;
            best_end = end1;
            best_len = end1 - start1;
        }
        
        // Try even-length palindrome centered between 'center' and 'center+1'
        if center + 1 < s.len() && s[center] == s[center + 1] {
            let (start2, end2) = expand_from_center_vec(&s, center, center + 2);
            if end2 - start2 > best_len {
                best_start = start2;
                best_end = end2;
                best_len = end2 - start2;
            }
        }
        
        center = center + 1;
    }
    
    // Extract the substring
    let mut result = Vec::<char>::new();
    let mut idx = best_start;
    while idx < best_end
        invariant
            best_start <= idx <= best_end,
            idx - best_start == result.len(),
            result@ == s@.subrange(best_start as int, idx as int),
        decreases best_end - idx,
    {
        result.push(s[idx]);
        idx = idx + 1;
    }
    
    (result, best_start, best_end)
}
// </vc-code>

fn main() {}

}