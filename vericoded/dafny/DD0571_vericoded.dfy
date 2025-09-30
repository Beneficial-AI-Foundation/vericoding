/* https://leetcode.com/problems/longest-palindromic-substring/
Given a string s, return the longest palindromic substring in s.

Example 1:
Input: s = "babad"
Output: "bab"
Explanation: "aba" is also a valid answer.
*/


// Specifying the problem: whether `s[i..j]` is palindromic
ghost predicate palindromic(s: string, i: int, j: int)
  requires 0 <= i <= j <= |s|
  decreases j - i
{
  j - i < 2 || (s[i] == s[j-1] && palindromic(s, i+1, j-1))
}

// A "common sense" about palindromes:

// A useful "helper function" that returns the longest palindrome at a given center (i0, j0).

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
method longestPalindrome'(s: string) returns (ans: string, lo: int, hi: int)
  ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi]
  ensures palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo
{
  assume{:axiom} false;
}


// Below are helper functions and lemmas we used:

// Inserts bogus characters to the original string (e.g. from `abc` to `|a|b|c|`).
// Note that this is neither efficient nor necessary in reality, but just for the ease of understanding.
function insert_bogus_chars(s: string, bogus: char): (s': string)
  ensures |s'| == 2 * |s| + 1
  ensures forall i | 0 <= i <= |s| :: s'[i * 2] == bogus
  ensures forall i | 0 <= i < |s| :: s'[i * 2 + 1] == s[i]
{
  if s == "" then
    [bogus]
  else
    var s'_old := insert_bogus_chars(s[1..], bogus);
    var s'_new := [bogus] + [s[0]] + s'_old;
    assert forall i | 1 <= i <= |s| :: s'_new[i * 2] == s'_old[(i-1) * 2];
    s'_new
}

// Returns (max_index, max_value) of array `a` starting from index `start`.
function argmax(a: array<int>, start: int): (res: (int, int))
  reads a
  requires 0 <= start < a.Length
  ensures start <= res.0 < a.Length && a[res.0] == res.1
  ensures forall i | start <= i < a.Length :: a[i] <= res.1
  decreases a.Length - start
{
  if start == a.Length - 1 then
    (start, a[start])
  else
    var (i, v) := argmax(a, start + 1);
    if a[start] >= v then (start, a[start]) else (i, v)
}

// Whether an interval at center `c` with a radius `r` is within the boundary of `s'`.
ghost predicate inbound_radius(s': string, c: int, r: int)
{
  r >= 0 && 0 <= c-r && c+r < |s'|
}

// Whether `r` is a valid palindromic radius at center `c`.
ghost predicate palindromic_radius(s': string, c: int, r: int)
  requires inbound_radius(s', c, r)
{
  palindromic(s', c-r, c+r+1)
}

// Whether `r` is the maximal palindromic radius at center `c`.
ghost predicate max_radius(s': string, c: int, r: int)
{
  && inbound_radius(s', c, r)
  && palindromic_radius(s', c, r)
  && (forall r' | r' > r && inbound_radius(s', c, r') :: !palindromic_radius(s', c, r'))
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
ghost function abs(x: int): int {
  if x >= 0 then x else -x
}

// Transfering our final result on `s'` to that on `s`:

// The following returns whether `s[lo..hi]` is the longest palindrome s.t. `lo + hi == k`:
ghost predicate max_interval_for_same_center(s: string, k: int, lo: int, hi: int) {
  && 0 <= lo <= hi <= |s|
  && lo + hi == k
  && palindromic(s, lo, hi)
  && (forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == k :: j - i <= hi - lo)
}

// Establishes the "palindromic isomorphism" between `s` and `s'`.

// Implies that whenever `c + r` is odd, the corresponding palindrome can be "lengthened for free"
// because its both ends are the bogus char.

// <vc-helpers>
// Helper lemma to show that if we can't expand further, we have the maximum palindrome for this center
lemma lemma_cannot_expand_is_maximal(s: string, lo: int, hi: int, i0: int, j0: int)
  requires 0 <= lo <= i0 <= j0 <= hi <= |s|
  requires palindromic(s, lo, hi)
  requires i0 + j0 == lo + hi  // same center
  requires lo == 0 || hi == |s| || s[lo-1] != s[hi]
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == i0 + j0 :: j - i <= hi - lo
{
  // By contradiction: suppose there exists a larger palindrome with the same center
  if exists i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == i0 + j0 :: j - i > hi - lo {
    var i, j :| 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == i0 + j0 && j - i > hi - lo;
    
    // Since they have the same center and j - i > hi - lo, we must have i < lo and j > hi
    assert i + j == lo + hi;
    assert j - i > hi - lo;
    
    // This means i < lo and j > hi
    assert i < lo;
    assert j > hi;
    
    // Now we need to show this leads to a contradiction
    // We'll use the containment property of palindromes
    lemma_palindrome_contains_smaller(s, i, j, lo, hi);
  }
}

// Helper lemma: if a palindrome contains another palindrome with the same center,
// and we can't expand the inner one, then the outer one can't exist
lemma lemma_palindrome_contains_smaller(s: string, i: int, j: int, lo: int, hi: int)
  requires 0 <= i < lo <= hi < j <= |s|
  requires palindromic(s, i, j)
  requires palindromic(s, lo, hi)
  requires i + j == lo + hi  // same center
  requires lo > 0 && hi < |s| && s[lo-1] != s[hi]
  ensures false
{
  // Since s[i..j] is palindromic and contains s[lo..hi] with the same center,
  // and i < lo and j > hi, we know that s[lo-1] and s[hi] are within s[i..j]
  
  // Calculate the positions: since palindromes are symmetric around their center,
  // s[lo-1] corresponds to s[hi] in the palindrome s[i..j]
  var center := (i + j) / 2;  // This might not be an integer position, but the logic still holds
  
  // The key insight: in a palindrome, positions equidistant from the center must be equal
  // lo-1 and hi are equidistant from the center (since (lo-1) + (hi+1) = lo + hi = i + j)
  
  // We can prove this by induction on the palindrome structure
  lemma_palindrome_symmetry(s, i, j, lo-1, hi);
  
  assert s[lo-1] == s[hi];
  assert false;  // Contradiction with the precondition
}

// Helper lemma about palindrome symmetry
lemma lemma_palindrome_symmetry(s: string, i: int, j: int, p1: int, p2: int)
  requires 0 <= i <= j <= |s|
  requires palindromic(s, i, j)
  requires i <= p1 < p2 < j
  requires p1 + p2 + 1 == i + j  // p1 and p2 are equidistant from center
  ensures s[p1] == s[p2]
  decreases j - i
{
  if j - i < 2 {
    // Base case: impossible since p1 < p2 requires at least 2 characters
    assert false;
  } else {
    // Recursive case
    assert s[i] == s[j-1];  // By definition of palindromic
    
    if p1 == i && p2 == j-1 {
      // Direct from palindrome definition
      assert s[p1] == s[p2];
    } else if p1 > i && p2 < j-1 {
      // Both are internal, recurse
      assert palindromic(s, i+1, j-1);
      lemma_palindrome_symmetry(s, i+1, j-1, p1, p2);
    } else {
      // This case shouldn't happen given our constraints
      assert false;
    }
  }
}

// Helper to show that expanding maintains the center
lemma lemma_expand_maintains_center(i0: int, j0: int, lo: int, hi: int)
  requires i0 - 1 == lo && j0 + 1 == hi
  ensures i0 + j0 == lo + hi
{
  // Simple arithmetic
}
// </vc-helpers>

// <vc-spec>
method expand_from_center(s: string, i0: int, j0: int) returns (lo: int, hi: int)
  requires 0 <= i0 <= j0 <= |s|
  requires palindromic(s, i0, j0)
  ensures 0 <= lo <= hi <= |s| && palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j)  // Among all palindromes
    && i + j == i0 + j0                                             // sharing the same center,
    :: j - i <= hi - lo                                             // `s[lo..hi]` is longest.
// </vc-spec>
// <vc-code>
{
  lo := i0;
  hi := j0;
  
  // Expand while we can
  while lo > 0 && hi < |s| && s[lo-1] == s[hi]
    invariant 0 <= lo <= i0 <= j0 <= hi <= |s|
    invariant palindromic(s, lo, hi)
    invariant i0 + j0 == lo + hi  // maintains the same center
    decreases lo
  {
    lo := lo - 1;
    hi := hi + 1;
    
    // Prove that the new interval is still palindromic
    assert s[lo] == s[hi-1];  // We just checked this in the loop condition
    assert palindromic(s, lo+1, hi-1);  // This was true before the update
    assert palindromic(s, lo, hi);  // By definition of palindromic
    
    // Prove that the center is maintained
    lemma_expand_maintains_center(lo+1, hi-1, lo, hi);
  }
  
  // At this point, we cannot expand further
  lemma_cannot_expand_is_maximal(s, lo, hi, i0, j0);
}
// </vc-code>

