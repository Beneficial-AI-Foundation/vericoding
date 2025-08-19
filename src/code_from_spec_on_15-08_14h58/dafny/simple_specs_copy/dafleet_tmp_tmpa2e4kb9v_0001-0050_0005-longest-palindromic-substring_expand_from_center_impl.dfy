//IMPL
/* code modified by LLM (iteration 1): Fixed index bounds in palindromic predicate to ensure array accesses are within valid range */
predicate palindromic(s: string, i: int, j: int)
  requires 0 <= i <= j <= |s|
{
  forall k | i <= k < i + (j - i) / 2 + 1 && k < |s| && j - 1 - (k - i) >= 0 && j - 1 - (k - i) < |s| :: s[k] == s[j - 1 - (k - i)]
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
  lo := i0;
  hi := j0;
  
  while lo > 0 && hi < |s| && s[lo - 1] == s[hi]
    invariant 0 <= lo <= hi <= |s|
    invariant lo + hi == i0 + j0
    invariant palindromic(s, lo, hi)
  {
    lo := lo - 1;
    hi := hi + 1;
  }
}