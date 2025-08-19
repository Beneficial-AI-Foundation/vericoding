//ATOM

// Define the palindromic predicate
predicate palindromic(s: string, i: int, j: int)
  requires 0 <= i <= j <= |s|
{
  forall k | 0 <= k < (j - i) / 2 :: s[i + k] == s[j - 1 - k]
}

// A useful "helper function" that returns the longest palindrome at a given center (i0, j0).
method expand_from_center(s: string, i0: int, j0: int) returns (lo: int, hi: int)
 requires 0 <= i0 <= j0 <= |s|
 requires palindromic(s, i0, j0)
 ensures 0 <= lo <= hi <= |s| && palindromic(s, lo, hi)
 ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) // Among all palindromes
  && i + j == i0 + j0                       // sharing the same center,
  :: j - i <= hi - lo                       // `s[lo..hi]` is longest.
{
  /* code modified by LLM (iteration 1): implemented actual expansion logic instead of assumes */
  lo := i0;
  hi := j0;
  
  // Expand outward while characters match
  while lo > 0 && hi < |s| && s[lo - 1] == s[hi]
    invariant 0 <= lo <= hi <= |s|
    invariant palindromic(s, lo, hi)
    invariant lo + hi == i0 + j0
  {
    lo := lo - 1;
    hi := hi + 1;
  }
}

//IMPL longestPalindrome

// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.
method longestPalindrome(s: string) returns (ans: string, lo: int, hi: int)
 ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi] // `ans` is indeed a substring in `s`
 ensures palindromic(s, lo, hi) // `ans` is palindromic
 ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo // `ans` is longest
{
  if |s| == 0 {
    lo := 0;
    hi := 0;
    ans := "";
    return;
  }
  
  /* code modified by LLM (iteration 2): fixed center expansion logic and loop invariants */
  // Initialize with single character palindrome
  lo := 0;
  hi := 1;
  
  // Check all possible centers (both character centers and between-character centers)
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= lo <= hi <= |s|
    invariant palindromic(s, lo, hi)
    invariant hi - lo >= 1  // At least one character
    invariant forall x, y | 0 <= x <= y <= |s| && palindromic(s, x, y) && 
              (exists c | 0 <= c < i :: (x + y == 2 * c + 1) || (x + y == 2 * c)) :: y - x <= hi - lo
  {
    // Check odd-length palindromes centered at i
    var odd_lo, odd_hi := expand_from_center(s, i, i + 1);
    if odd_hi - odd_lo > hi - lo {
      lo := odd_lo;
      hi := odd_hi;
    }
    
    // Check even-length palindromes centered between i and i+1
    if i + 1 < |s| && s[i] == s[i + 1] {
      var even_lo, even_hi := expand_from_center(s, i, i + 2);
      if even_hi - even_lo > hi - lo {
        lo := even_lo;
        hi := even_hi;
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