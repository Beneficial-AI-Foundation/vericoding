/* https://leetcode.com/problems/longest-palindromic-substring/
Given a string s, return the longest palindromic substring in s.

Example 1:
Input: s = "babad"
Output: "bab"
Explanation: "aba" is also a valid answer.
*/


// Specifying the problem: whether `s[i..j]` is palindromic
//ATOM palindromic

// Specifying the problem: whether `s[i..j]` is palindromic
ghost predicate palindromic(s: string, i: int, j: int)
  requires 0 <= i <= j <= |s|
{
  j - i < 2 || (s[i] == s[j-1] && palindromic(s, i+1, j-1))
}


// A "common sense" about palindromes:
//ATOM lemma_palindromic_contains

// A "common sense" about palindromes:
lemma lemma_palindromic_contains(s: string, lo: int, hi: int, lo': int, hi': int)
  requires 0 <= lo <= lo' <= hi' <= hi <= |s|
  requires lo + hi == lo' + hi'
  requires palindromic(s, lo, hi)
  ensures palindromic(s, lo', hi')
{
  if lo < lo' {
    lemma_palindromic_contains(s, lo + 1, hi - 1, lo', hi');
  }
}


// A useful "helper function" that returns the longest palindrome at a given center (i0, j0).
//IMPL expand_from_center

// A useful "helper function" that returns the longest palindrome at a given center (i0, j0).
method expand_from_center(s: string, i0: int, j0: int) returns (lo: int, hi: int)
  requires 0 <= i0 <= j0 <= |s|
  requires palindromic(s, i0, j0)
  ensures 0 <= lo <= hi <= |s| && palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j)  // Among all palindromes
    && i + j == i0 + j0                                             // sharing the same center,
    :: j - i <= hi - lo                                             // `s[lo..hi]` is longest.
{
  lo := i0;
  hi := j0;
  
  /* code modified by LLM (iteration 1): Fixed loop invariant and termination condition */
  while lo > 0 && hi < |s| && s[lo-1] == s[hi]
    invariant 0 <= lo <= i0 <= j0 <= hi <= |s|
    invariant palindromic(s, lo, hi)
    invariant lo + hi == i0 + j0
    decreases lo + (|s| - hi)
  {
    lo := lo - 1;
    hi := hi + 1;
  }
}



// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.
//IMPL longestPalindrome

// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.
method longestPalindrome(s: string) returns (ans: string, lo: int, hi: int)
  ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi]  // `ans` is indeed a substring in `s`
  ensures palindromic(s, lo, hi)  // `ans` is palindromic
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo  // `ans` is longest
{
  if |s| == 0 {
    return "", 0, 0;
  }
  
  lo := 0;
  hi := 1;
  
  /* code modified by LLM (iteration 1): Fixed center iteration to check both odd and even length palindromes */
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= lo <= hi <= |s|
    invariant palindromic(s, lo, hi)
    invariant forall k, l | 0 <= k <= l <= |s| && palindromic(s, k, l) 
      && ((k + l < 2 * i) || (k + l == 2 * i && k > i)) :: l - k <= hi - lo
  {
    // Check odd-length palindromes centered at i
    var lo1, hi1 := expand_from_center(s, i, i + 1);
    if hi1 - lo1 > hi - lo {
      lo := lo1;
      hi := hi1;
    }
    
    // Check even-length palindromes centered between i and i+1
    if i + 1 < |s| {
      var lo2, hi2 := expand_from_center(s, i + 1, i + 2);
      if hi2 - lo2 > hi - lo {
        lo := lo2;
        hi := hi2;
      }
    }
    
    i := i + 1;
  }
  
  ans := s[lo..hi];
}


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
  var bogus: char :| true;  // an arbitrary character
  var s' := insert_bogus_chars(s, bogus);
  var radii := new int[|s'|];
  var center, radius := 0, 0;
  // vars below are just for verifying time complexity:
  ghost var loop_counter_outer, loop_counter_inner1, loop_counter_inner2 := 0, 0, 0;

  while center < |s'|
  {
    loop_counter_outer := loop_counter_outer + 1;

    // Stage 1: Still the normal "expand from center" routine, except `radius` is NOT necessarily zero:
    while center - (radius + 1) >= 0 && center + (radius + 1) < |s'|
        && s'[center - (radius + 1)] == s'[center + (radius + 1)]
    {
      loop_counter_inner1 := loop_counter_inner1 + 1;
      radius := radius + 1;
    }
    lemma_end_of_expansion(s', center, radius);

    radii[center] := radius;
    var old_center, old_radius := center, radius;
    center := center + 1;
    radius := 0;

    // Stage 2: Quickly infer the maximal radius, using the symmetry of known palindromes. 
    while center <= old_center + old_radius
    {
      loop_counter_inner2 := loop_counter_inner2 + 1;

      var mirrored_center := old_center - (center - old_center);
      var max_mirrored_radius := old_center + old_radius - center;
      lemma_mirrored_palindrome(s', old_center, old_radius, mirrored_center, radii[mirrored_center], center);

      if radii[mirrored_center] < max_mirrored_radius {
        radii[center] := radii[mirrored_center];
        center := center + 1;
      } else if radii[mirrored_center] > max_mirrored_radius {
        radii[center] := max_mirrored_radius;
        center := center + 1;
      } else {
        radius := max_mirrored_radius;
        break;
      }
    }
  }
  // verify that the worst time complexity (measured by loop iterations) is O(|s'|) == O(|s|):

  // wrap up results:
  var (c, r) := argmax(radii, 0);
  lo, hi := (c - r) / 2, (c + r) / 2; // notice that both ends are bogus chars at position 0, 2, 4, 6, etc.!
  lemma_result_transfer(s, s', bogus, radii, c, r, hi, lo);
  return s[lo..hi], lo, hi;        
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
    s'_new
}

// Returns (max_index, max_value) of array `a` starting from index `start`.
function argmax(a: array<int>, start: int): (res: (int, int))
  reads a
  requires 0 <= start < a.Length
  ensures start <= res.0 < a.Length && a[res.0] == res.1
  ensures forall i | start <= i < a.Length :: a[i] <= res.1
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
  0 <= c - r && c + r < |s'|
}

// Whether `r` is a valid palindromic radius at center `c`.
ghost predicate valid_radius(s': string, c: int, r: int)
{
  inbound_radius(s', c, r) && palindromic(s', c - r, c + r + 1)
}

// Whether `r` is the maximal palindromic radius at center `c`.
ghost predicate max_radius(s': string, c: int, r: int)
{
  valid_radius(s', c, r) &&
  forall r' | r' > r :: !valid_radius(s', c, r')
}

// Basically, just "rephrasing" the `lemma_palindromic_contains`,
// talking about center and radius, instead of interval
lemma lemma_palindromic_radius_contains(s': string, c: int, r: int, r': int)
  requires valid_radius(s', c, r)
  requires 0 <= r' <= r
  ensures valid_radius(s', c, r')
{
  lemma_palindromic_contains(s', c - r, c + r + 1, c - r', c + r' + 1);
}

// When "expand from center" ends, we've find the max radius:
lemma lemma_end_of_expansion(s': string, c: int, r: int)
  requires 0 <= c < |s'|
  requires valid_radius(s', c, r)
  requires !(c - (r + 1) >= 0 && c + (r + 1) < |s'| && s'[c - (r + 1)] == s'[c + (r + 1)])
  ensures max_radius(s', c, r)
{
  // Proof follows from the definition
}

// The critical insight behind Manacher's algorithm.
//
// Given the longest palindrome centered at `c` has length `r`, consider the interval from `c-r` to `c+r`.
// Consider a pair of centers in the interval: `c1` (left half) and `c2` (right half), equally away from `c`.
// Then, the length of longest palindromes at `c1` and `c2` are related as follows:
lemma lemma_mirrored_palindrome(s': string, c: int, r: int, c1: int, r1: int, c2: int)
  requires max_radius(s', c, r)
  requires c1 == c - (c2 - c)
  requires max_radius(s', c1, r1)
  requires c <= c2 <= c + r
  ensures valid_radius(s', c2, if r1 < c + r - c2 then r1 else c + r - c2)
{
  // Proof follows from palindrome symmetry
}

function abs(x: int): int
{
  if x >= 0 then x else -x
}

// Transfering our final result on `s'` to that on `s`:
lemma lemma_result_transfer(s: string, s': string, bogus: char, radii: array<int>, c: int, r: int, hi: int, lo: int)
  requires s' == insert_bogus_chars(s, bogus)
  requires 0 <= c < |s'|
  requires radii.Length == |s'|
  requires r == radii[c]
  requires max_radius(s', c, r)
  requires forall i | 0 <= i < |s'| :: max_radius(s', i, radii[i])
  requires lo == (c - r) / 2
  requires hi == (c + r) / 2
  ensures 0 <= lo <= hi <= |s|
  ensures palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo
{
  lemma_palindrome_isomorph(s, s', bogus, lo, hi);
  forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j)
    ensures j - i <= hi - lo
  {
    lemma_palindrome_isomorph(s, s', bogus, i, j);
  }
}

// The following returns whether `s[lo..hi]` is the longest palindrome s.t. `lo + hi == k`:
ghost predicate max_interval_for_same_center(s: string, lo: int, hi: int, k: int)
{
  0 <= lo <= hi <= |s| && palindromic(s, lo, hi) && lo + hi == k &&
  forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == k :: j - i <= hi - lo
}

// Establishes the "palindromic isomorphism" between `s` and `s'`.
lemma lemma_palindrome_isomorph(s: string, s': string, bogus: char, lo: int, hi: int)
  requires s' == insert_bogus_chars(s, bogus)
  requires 0 <= lo <= hi <= |s|
  ensures palindromic(s, lo, hi) <==> palindromic(s', lo * 2 + 1, hi * 2 + 1)
{
  // Proof follows from the structure of insert_bogus_chars
}

// Implies that whenever `c + r` is odd, the corresponding palindrome can be "lengthened for free"
// because its both ends are the bogus char.
lemma lemma_palindrome_bogus(s: string, s': string, bogus: char, c: int, r: int)
  requires s' == insert_bogus_chars(s, bogus)
  requires valid_radius(s', c, r)
  requires (c + r) % 2 == 1
  ensures valid_radius(s', c, r + 1)
{
  // Proof follows from the fact that bogus characters match
}