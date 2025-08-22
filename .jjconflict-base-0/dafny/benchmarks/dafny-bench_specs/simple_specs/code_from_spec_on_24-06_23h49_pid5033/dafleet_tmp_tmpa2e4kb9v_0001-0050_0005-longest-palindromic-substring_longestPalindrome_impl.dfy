//ATOM

// Define the palindromic predicate
predicate palindromic(s: string, i: int, j: int)
  requires 0 <= i <= j <= |s|
{
  forall k | i <= k < j :: s[k] == s[j - 1 - (k - i)]
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
  lo := 0;
  hi := 0;
  assume 0 <= lo <= hi <= |s| && palindromic(s, lo, hi);
  assume forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) // Among all palindromes;
  return lo, hi;
}

//IMPL longestPalindrome

/* code modified by LLM (iteration 1): Added helper lemma to establish palindrome property from character matching */
lemma PalindromeFromMatching(s: string, left: int, right: int)
  requires 0 <= left <= right < |s|
  requires forall k | left <= k <= right :: s[k] == s[left + right - k]
  ensures palindromic(s, left, right + 1)
{
  // Proof that character matching implies palindromic property
}

/* code modified by LLM (iteration 1): Fixed expandAroundCenter method with proper bounds and palindrome verification */
method expandAroundCenter(s: string, left: int, right: int) returns (lo: int, hi: int)
  requires 0 <= left < |s| && 0 <= right < |s|
  ensures 0 <= lo <= hi <= |s|
  ensures palindromic(s, lo, hi)
{
  var l := left;
  var r := right;
  
  /* code modified by LLM (iteration 1): Check if initial center forms a palindrome */
  if s[l] != s[r] {
    lo := left;
    hi := left + 1;
    return;
  }
  
  /* code modified by LLM (iteration 1): Expand while maintaining palindrome property */
  while l > 0 && r < |s| - 1 && s[l - 1] == s[r + 1]
    invariant 0 <= l <= left
    invariant right <= r < |s|
    invariant s[l] == s[r]
    invariant forall k | l <= k <= r :: s[k] == s[l + r - k]
    decreases l
  {
    l := l - 1;
    r := r + 1;
  }
  
  lo := l;
  hi := r + 1;
  
  /* code modified by LLM (iteration 1): Apply lemma to establish palindromic property */
  PalindromeFromMatching(s, l, r);
}

/* code modified by LLM (iteration 1): Helper lemma for single character palindromes */
lemma SingleCharPalindrome(s: string, i: int)
  requires 0 <= i < |s|
  ensures palindromic(s, i, i + 1)
{
  // Single character is always a palindrome
}

/* code modified by LLM (iteration 1): Helper lemma for empty palindromes */
lemma EmptyPalindrome(s: string, i: int)
  requires 0 <= i <= |s|
  ensures palindromic(s, i, i)
{
  // Empty string is always a palindrome
}

// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.
method longestPalindrome(s: string) returns (ans: string, lo: int, hi: int)
 ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi] // `ans` is indeed a substring in `s`
 ensures palindromic(s, lo, hi) // `ans` is palindromic
 ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo // `ans` is longest
{
  if |s| == 0 {
    ans := "";
    lo := 0;
    hi := 0;
    /* code modified by LLM (iteration 1): Apply empty palindrome lemma */
    EmptyPalindrome(s, 0);
    return;
  }
  
  /* code modified by LLM (iteration 1): Initialize with first character */
  ans := s[0..1];
  lo := 0;
  hi := 1;
  SingleCharPalindrome(s, 0);
  
  /* code modified by LLM (iteration 1): Iterate through all possible centers */
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= lo <= hi <= |s| && ans == s[lo..hi]
    invariant palindromic(s, lo, hi)
    invariant forall l, r | 0 <= l <= r <= |s| && palindromic(s, l, r) :: 
              (exists c :: 0 <= c < i && (l + r == 2 * c || l + r == 2 * c + 1)) ==> r - l <= hi - lo
  {
    /* code modified by LLM (iteration 1): Check odd-length palindromes centered at i */
    var odd_lo, odd_hi := expandAroundCenter(s, i, i);
    if odd_hi - odd_lo > hi - lo {
      lo := odd_lo;
      hi := odd_hi;
      ans := s[lo..hi];
    }
    
    /* code modified by LLM (iteration 1): Check even-length palindromes centered between i and i+1 */
    if i + 1 < |s| {
      var even_lo, even_hi := expandAroundCenter(s, i, i + 1);
      if even_hi - even_lo > hi - lo {
        lo := even_lo;
        hi := even_hi;
        ans := s[lo..hi];
      }
    }
    
    i := i + 1;
  }
}