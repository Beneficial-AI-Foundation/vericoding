//ATOM

// A useful "helper function" that returns the longest palindrome at a given center (i0, j0).
method expand_from_center(s: string, i0: int, j0: int) returns (lo: int, hi: int)
 requires 0 <= i0 <= j0 <= |s|
 requires palindromic(s, i0, j0)
 ensures 0 <= lo <= hi <= |s| && palindromic(s, lo, hi)
 ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) // Among all palindromes
  && i + j == i0 + j0                       // sharing the same center,
  :: j - i <= hi - lo                       // `s[lo..hi]` is longest.
{
  lo := 0;
  hi := 0;
  assume 0 <= lo <= hi <= |s| && palindromic(s, lo, hi);
  assume forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) // Among all palindromes;
  return lo, hi;
}


// SPEC


// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.
method longestPalindrome(s: string) returns (ans: string, lo: int, hi: int)
 ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi] // `ans` is indeed a substring in `s`
 ensures palindromic(s, lo, hi) // `ans` is palindromic
 ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo // `ans` is longest
{
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