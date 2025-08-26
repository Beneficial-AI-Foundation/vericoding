// <vc-spec>
method longestPalindrome(s: string) returns (ans: string)
  requires |s| > 0
  ensures |ans| > 0
  ensures palindromic(s, 0, |s|) ==> ans == s
  ensures exists lo, hi :: 0 <= lo <= hi <= |s| && ans == s[lo..hi] && palindromic(s, lo, hi)
  ensures forall lo', hi' :: 0 <= lo' <= hi' <= |s| && palindromic(s, lo', hi') ==> |ans| >= hi' - lo'
// </vc-spec>

// <vc-helpers>
predicate palindromic(s: string, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
{
  forall i :: lo <= i < lo + (hi - lo) / 2 ==> s[i] == s[hi - 1 - (i - lo)]
}

method expand_from_center(s: string, left: int, right: int) returns (lo: int, hi: int)
  requires 0 <= left < |s| && 0 <= right < |s|
  ensures 0 <= lo <= hi <= |s|
  ensures palindromic(s, lo, hi)
  ensures left <= right ==> lo <= left && right < hi
{
  var l, r := left, right;
  while l >= 0 && r < |s| && s[l] == s[r]
    invariant l <= left && right <= r
    invariant l >= 0 && r < |s| ==> s[l] == s[r]
    invariant forall i :: l + 1 <= i <= r - 1 ==> s[i] == s[l + r - i]
    decreases l + (|s| - 1 - r)
  {
    l := l - 1;
    r := r + 1;
  }
  lo := l + 1;
  hi := r;
  
  // Prove palindromic property
  assert forall i :: lo <= i < lo + (hi - lo) / 2 ==> s[i] == s[hi - 1 - (i - lo)];
}
// </vc-helpers>

// <vc-code>
{
  var lo, hi := 0, 1;  // Initially, first character is longest palindrome;
  var i := 0;
  
  // Prove initial palindrome
  assert palindromic(s, 0, 1);
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= lo <= hi <= |s| && palindromic(s, lo, hi)
    invariant hi - lo > 0
    invariant forall lo', hi' :: 0 <= lo' <= hi' <= |s| && palindromic(s, lo', hi') && 
              (exists j :: 0 <= j < i && ((lo' <= j <= hi' - 1) || (lo' <= j < hi' && lo' <= j + 1 <= hi' - 1))) 
              ==> hi' - lo' <= hi - lo
  {
    // Odd length palindromes centered at i
    var lo1, hi1 := expand_from_center(s, i, i);
    if hi1 - lo1 > hi - lo {
      lo, hi := lo1, hi1;
    }
    
    // Even length palindromes centered between i and i+1
    if i + 1 < |s| {
      var lo2, hi2 := expand_from_center(s, i, i + 1);
      if hi2 - lo2 > hi - lo {
        lo, hi := lo2, hi2;
      }
    }
    
    i := i + 1;
  }
  
  // Assert final properties
  assert 0 <= lo <= hi <= |s| && palindromic(s, lo, hi);
  ans := s[lo..hi];
  assert |ans| == hi - lo;
  assert |ans| > 0;
}
// </vc-code>