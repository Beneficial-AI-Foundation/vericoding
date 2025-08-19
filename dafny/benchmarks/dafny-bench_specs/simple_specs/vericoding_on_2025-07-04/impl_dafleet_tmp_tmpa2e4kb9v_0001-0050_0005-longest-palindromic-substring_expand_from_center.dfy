//IMPL

/* code modified by LLM (iteration 4): Added palindromic predicate definition */
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
    lo := i0;
    hi := j0;
    
    /* code modified by LLM (iteration 4): Loop with proper invariants */
    while lo > 0 && hi < |s| && s[lo-1] == s[hi]
        invariant 0 <= lo <= hi <= |s|
        invariant palindromic(s, lo, hi)
        invariant lo + hi == i0 + j0
        invariant lo <= i0 && j0 <= hi
        decreases lo + (|s| - hi)
    {
        lo := lo - 1;
        hi := hi + 1;
    }
    
    /* code modified by LLM (iteration 4): Added lemma call to establish maximality */
    establish_maximality(s, i0, j0, lo, hi);
}

/* code modified by LLM (iteration 4): Simplified and corrected helper lemma */
lemma establish_maximality(s: string, i0: int, j0: int, lo: int, hi: int)
  requires 0 <= i0 <= j0 <= |s|
  requires 0 <= lo <= hi <= |s|
  requires palindromic(s, i0, j0)
  requires palindromic(s, lo, hi)
  requires lo + hi == i0 + j0
  requires lo <= i0 && j0 <= hi
  requires lo == 0 || hi == |s| || s[lo-1] != s[hi]
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == i0 + j0 :: j - i <= hi - lo
{
    forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == i0 + j0
    ensures j - i <= hi - lo
    {
        if j - i > hi - lo {
            /* code modified by LLM (iteration 4): Direct contradiction proof */
            // From i + j == lo + hi and j - i > hi - lo
            // We get: i < lo and j > hi
            assert i + j == lo + hi;
            assert j - i > hi - lo;
            
            // Algebraically: 2*i = (i+j) - (j-i) < (lo+hi) - (hi-lo) = 2*lo
            assert i < lo;
            // Similarly: 2*j = (i+j) + (j-i) > (lo+hi) + (hi-lo) = 2*hi  
            assert j > hi;
            
            // If we can expand further, it contradicts the stopping condition
            if lo > 0 && hi < |s| {
                // Since s[i..j] is palindromic and i < lo, j > hi
                // We have s[i] == s[j-1] by palindrome property
                // Since i <= lo-1 and j-1 >= hi, we get s[lo-1] == s[hi]
                assert s[i] == s[j-1]; // palindrome property
                assert i <= lo - 1;
                assert j - 1 >= hi;
                
                if i == lo - 1 && j - 1 == hi {
                    assert s[lo-1] == s[hi];
                    assert false; // contradicts precondition
                } else {
                    // Use transitivity of palindrome to show s[lo-1] == s[hi]
                    palindrome_transitivity(s, i, j, lo-1, hi);
                    assert false;
                }
            }
        }
    }
}

/* code modified by LLM (iteration 4): Corrected helper lemma for palindrome transitivity */
lemma palindrome_transitivity(s: string, i: int, j: int, k1: int, k2: int)
  requires 0 <= i <= j <= |s|
  requires palindromic(s, i, j)
  requires i <= k1 < j && i <= k2 < j
  requires k1 + k2 == i + j - 1
  ensures s[k1] == s[k2]
{
    // In palindrome s[i..j], positions that are symmetric about center are equal
    var center_sum := i + j - 1;
    assert k1 + k2 == center_sum;
    
    // k1 and k2 are symmetric positions in the palindrome
    var pos1 := k1 - i;
    var pos2 := k2 - i;
    assert pos1 + pos2 == j - i - 1;
    
    // By palindrome definition
    assert s[i + pos1] == s[j - 1 - pos1];
    assert k2 == i + pos2 == i + (j - i - 1 - pos1) == j - 1 - pos1;
    assert s[k1] == s[k2];
}