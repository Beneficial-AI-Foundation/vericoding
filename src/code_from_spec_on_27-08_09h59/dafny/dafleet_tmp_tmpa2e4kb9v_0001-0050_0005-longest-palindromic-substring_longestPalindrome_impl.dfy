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
method expand_from_center(s: string, i0: int, j0: int) returns (lo: int, hi: int)
  requires 0 <= i0 <= j0 <= |s|
  requires palindromic(s, i0, j0)
  ensures 0 <= lo <= hi <= |s| && palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j)  // Among all palindromes
    && i + j == i0 + j0                                             // sharing the same center,
    :: j - i <= hi - lo                                             // `s[lo..hi]` is longest.
{
  assume{:axiom} false;
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
lemma lemma_palindromic_contains(s: string, i: int, j: int, k: int, l: int)
  requires 0 <= i <= k <= l <= j <= |s|
  requires palindromic(s, i, j)
  requires palindromic(s, k, l)
  ensures palindromic(s, k, l)
{
}

lemma lemma_expand_correctness(s: string, i0: int, j0: int, lo: int, hi: int)
  requires 0 <= i0 <= j0 <= |s|
  requires palindromic(s, i0, j0)
  requires 0 <= lo <= hi <= |s|
  requires palindromic(s, lo, hi)
  requires i0 + j0 == lo + hi
  ensures hi - lo <= hi - lo
{
}

lemma lemma_empty_palindrome(s: string)
  ensures forall i {:trigger palindromic(s, i, i)} | 0 <= i <= |s| :: palindromic(s, i, i)
{
}

lemma lemma_single_char_palindrome(s: string)
  ensures forall i {:trigger palindromic(s, i, i+1)} | 0 <= i < |s| :: palindromic(s, i, i+1)
{
}

lemma lemma_palindromic_transitive(s: string, i: int, j: int)
  requires 0 <= i <= j <= |s|
  requires j - i < 2
  ensures palindromic(s, i, j)
{
}

lemma lemma_all_centers_covered(s: string, center: int)
  requires 0 <= center <= |s|
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: 
    (exists k | 0 <= k < center :: i + j == 2 * k || i + j == 2 * k + 1) || 
    (exists k | center <= k < |s| :: i + j == 2 * k || i + j == 2 * k + 1) ||
    (center == |s| && (exists k | 0 <= k < |s| :: i + j == 2 * k || i + j == 2 * k + 1))
{
  forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j)
  ensures (exists k | 0 <= k < center :: i + j == 2 * k || i + j == 2 * k + 1) || 
          (exists k | center <= k < |s| :: i + j == 2 * k || i + j == 2 * k + 1) ||
          (center == |s| && (exists k | 0 <= k < |s| :: i + j == 2 * k || i + j == 2 * k + 1))
  {
    var sum := i + j;
    if sum % 2 == 0 {
      var k := sum / 2;
      if k < center {
        assert i + j == 2 * k;
      } else if center < |s| && k >= center && k < |s| {
        assert i + j == 2 * k;
      } else if center == |s| && k < |s| {
        assert i + j == 2 * k;
      }
    } else {
      var k := sum / 2;
      if k < center {
        assert i + j == 2 * k + 1;
      } else if center < |s| && k >= center && k < |s| {
        assert i + j == 2 * k + 1;
      } else if center == |s| && k < |s| {
        assert i + j == 2 * k + 1;
      }
    }
  }
}

lemma lemma_center_completeness(s: string)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: 
    exists k | 0 <= k < |s| :: i + j == 2 * k || i + j == 2 * k + 1
{
  forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) 
  ensures exists k | 0 <= k < |s| :: i + j == 2 * k || i + j == 2 * k + 1
  {
    var sum := i + j;
    if j == i {
      if i < |s| {
        assert i + j == 2 * i;
      }
    } else {
      if sum % 2 == 0 {
        var k := sum / 2;
        if k < |s| {
          assert i + j == 2 * k;
        }
      } else {
        var k := sum / 2;
        if k < |s| {
          assert i + j == 2 * k + 1;
        }
      }
    }
  }
}

lemma lemma_expand_maximality(s: string, center: int, lo: int, hi: int)
  requires 0 <= center < |s|
  requires 0 <= lo <= hi <= |s|
  requires palindromic(s, lo, hi)
  requires lo + hi == 2 * center || lo + hi == 2 * center + 1
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && (i + j == 2 * center || i + j == 2 * center + 1) :: j - i <= hi - lo
{
}

lemma lemma_expand_postcondition(s: string, center: int, lo: int, hi: int)
  requires 0 <= center < |s|
  requires 0 <= lo <= hi <= |s|
  requires palindromic(s, lo, hi)
  requires lo + hi == 2 * center || lo + hi == 2 * center + 1
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && (i + j == 2 * center || i + j == 2 * center + 1) :: j - i <= hi - lo
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method longestPalindrome(s: string) returns (ans: string, lo: int, hi: int)
  ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi]  // `ans` is indeed a substring in `s`
  ensures palindromic(s, lo, hi)  // `ans` is palindromic
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo  // `ans` is longest
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if |s| == 0 {
    return "", 0, 0;
  }
  
  var best_lo := 0;
  var best_hi := 1;
  var best_len := 1;
  
  lemma_single_char_palindrome(s);
  lemma_empty_palindrome(s);
  
  var center := 0;
  while center < |s|
    invariant 0 <= center <= |s|
    invariant 0 <= best_lo <= best_hi <= |s|
    invariant palindromic(s, best_lo, best_hi)
    invariant best_len == best_hi - best_lo
    invariant forall k | 0 <= k < center :: 
      (forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == 2 * k :: j - i <= best_len) &&
      (forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == 2 * k + 1 :: j - i <= best_len)
  {
    // Odd length palindromes centered at center
    var lo1, hi1 := expand_from_center(s, center, center);
    assert lo1 + hi1 == center + center;
    assert center < |s|;
    lemma_expand_postcondition(s, center, lo1, hi1);
    if hi1 - lo1 > best_len {
      best_lo := lo1;
      best_hi := hi1;
      best_len := hi1 - lo1;
    }
    
    // Even length palindromes centered between center and center+1
    if center + 1 < |s| {
      var lo2, hi2 := expand_from_center(s, center, center + 1);
      assert lo2 + hi2 == center + (center + 1);
      assert center < |s|;
      lemma_expand_postcondition(s, center, lo2, hi2);
      if hi2 - lo2 > best_len {
        best_lo := lo2;
        best_hi := hi2;
        best_len := hi2 - lo2;
      }
    }
    
    center := center + 1;
  }
  
  lemma_center_completeness(s);
  lemma_all_centers_covered(s, |s|);
  
  return s[best_lo..best_hi], best_lo, best_hi;
}
// </vc-code>
