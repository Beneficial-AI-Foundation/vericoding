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
lemma shrink_palindrome(s: string, i: int, j: int, i2: int, j2: int)
  requires 0 <= i <= i2 <= j2 <= j <= |s|
  requires palindromic(s, i, j)
  requires i + j == i2 + j2
  ensures palindromic(s, i2, j2)
  decreases j - i
{
  if j - i < 2 {
    // then any inner interval has length < 2 and is palindromic by definition
  } else {
    // From palindromic(s,i,j) and j-i >= 2 we get s[i] == s[j-1] and palindromic(s, i+1, j-1)
    assert palindromic(s, i+1, j-1);

    // If (i2,j2) is exactly (i,j) then we're done.
    if i2 == i {
      // then by sum equality j2 == j, and palindromic(s,i2,j2) follows immediately
    } else if j2 == j {
      // symmetric case: then i2 == i, handled above; keep for clarity
    } else {
      // Otherwise, both i2 > i and j2 < j must hold (because i+j == i2 + j2).

      // We are in the branch where j2 != j and j2 <= j, hence j2 < j.
      assert j2 <= j;
      assert j2 != j;
      if j2 >= j {
        // from j2 <= j and j2 >= j we get j2 == j contradicting j2 != j
        assert j2 == j;
        assert false;
      }
      assert j2 < j;

      // Prove i < i2
      assert i2 == i + j - j2;
      assert j - j2 > 0;
      assert i2 > i;

      // Now show the preconditions for the recursive call hold:
      assert 0 <= i+1;
      assert i+1 <= i2;          // from i < i2
      assert i2 <= j2;           // from requires
      assert j2 <= j-1;          // from j2 < j
      assert j-1 <= |s|;         // from j <= |s|
      shrink_palindrome(s, i+1, j-1, i2, j2);
    }
  }
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
  var k := i0 + j0;
  lo := i0;
  hi := j0;
  while lo > 0 && hi < |s| && s[lo-1] == s[hi]
    invariant 0 <= lo <= i0
    invariant j0 <= hi <= |s|
    invariant lo + hi == k
    invariant palindromic(s, lo, hi)
    decreases lo
  {
    lo := lo - 1;
    hi := hi + 1;
  }

  // Prove maximality among palindromes sharing the same center by contradiction:
  if exists i, j :: 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == k && j - i > hi - lo {
    var i, j :| 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == k && j - i > hi - lo;
    // basic equalities
    assert i + j == k;
    assert lo + hi == k;
    assert j - i > hi - lo;

    // show i < lo
    if !(i < lo) {
      assert i >= lo;
      assert j == k - i;
      assert hi == k - lo;
      assert j <= hi;
      assert j - i <= hi - lo;
      assert false;
    }
    assert i < lo;

    // show j > hi
    if !(j > hi) {
      assert j <= hi;
      assert j == k - i;
      assert hi == k - lo;
      assert i >= lo;
      assert j - i <= hi - lo;
      assert false;
    }
    assert j > hi;

    // from i < lo and j > hi we get lo > 0 and hi < |s|
    assert lo > 0;
    assert hi < |s|;

    // we can shrink (i,j) to (lo-1, hi+1)
    assert 0 <= i <= lo - 1 <= hi + 1 <= j <= |s|;
    assert i + j == (lo - 1) + (hi + 1);
    shrink_palindrome(s, i, j, lo - 1, hi + 1);
    assert palindromic(s, lo - 1, hi + 1);
    // hence the expansion condition would hold, contradicting loop exit
    assert s[lo - 1] == s[hi];
    assert lo > 0 && hi < |s| && s[lo - 1] == s[hi];
    assert false;
  }

  assert forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == k :: j - i <= hi - lo;
}
// </vc-code>

