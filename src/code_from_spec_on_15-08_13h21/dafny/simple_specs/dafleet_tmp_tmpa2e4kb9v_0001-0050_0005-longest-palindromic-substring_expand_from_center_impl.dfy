predicate palindromic(s: string, i: int, j: int)
  requires 0 <= i <= j <= |s|
{
  /* code modified by LLM (iteration 3): Added explicit trigger to fix quantifier warning */
  forall k {:trigger s[i + k], s[j - 1 - k]} | 0 <= k < (j - i) / 2 :: s[i + k] == s[j - 1 - k]
}

//IMPL
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
  
  /* code modified by LLM (iteration 4): Fixed invariant issues by establishing proper base case and maintenance */
  while lo > 0 && hi < |s| && s[lo - 1] == s[hi]
    invariant 0 <= lo <= hi <= |s|
    invariant lo + hi == i0 + j0
    invariant palindromic(s, lo, hi)
    invariant forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == i0 + j0 :: j - i <= hi - lo
    decreases lo
  {
    /* code modified by LLM (iteration 4): Store old values and prove palindromicity step by step */
    var old_lo := lo;
    var old_hi := hi;
    
    assert s[lo - 1] == s[hi]; // From loop condition
    
    lo := lo - 1;
    hi := hi + 1;
    
    /* code modified by LLM (iteration 4): Prove palindromicity by cases */
    assert palindromic(s, old_lo, old_hi); // From loop invariant
    
    // Prove the new range is palindromic
    forall k | 0 <= k < (hi - lo) / 2
      ensures s[lo + k] == s[hi - 1 - k]
    {
      if k == 0 {
        // First character: s[lo] == s[hi - 1]
        assert s[lo] == s[old_lo - 1] == s[old_hi] == s[hi - 1];
      } else if k == (hi - lo) / 2 - 1 && (hi - lo) % 2 == 0 {
        // Last character for even length
        assert lo + k == old_hi - 1;
        assert hi - 1 - k == old_lo;
        assert s[lo + k] == s[old_hi - 1];
        assert s[hi - 1 - k] == s[old_lo];
        assert s[old_lo] == s[old_hi - 1]; // From old palindrome
      } else {
        // Middle characters: use old palindrome property
        assert 1 <= k <= (hi - lo) / 2 - 1;
        assert lo + k == old_lo + k - 1;
        assert hi - 1 - k == old_hi - k + 1 - 1;
        assert 0 <= k - 1 < (old_hi - old_lo) / 2;
        assert s[old_lo + (k-1)] == s[old_hi - 1 - (k-1)]; // From old palindrome
        assert s[lo + k] == s[hi - 1 - k];
      }
    }
    
    assert palindromic(s, lo, hi);
    
    /* code modified by LLM (iteration 4): Prove maximality is maintained */
    forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == i0 + j0
      ensures j - i <= hi - lo
    {
      if j - i > old_hi - old_lo {
        // This would contradict the old maximality, so impossible
        assert false;
      } else {
        // Use old maximality invariant
        assert j - i <= old_hi - old_lo < hi - lo;
      }
    }
  }
}