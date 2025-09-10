function isPalindrome(s: string): bool
{
    forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}

// <vc-helpers>
lemma PalindromeSubstrings(s: string, k: int, len: int)
  requires k > 0
  requires |s| % k == 0
  requires len == |s| / k
{
}

function IsPalSubrange(s: string, start: int, end: int): bool
  requires 0 <= start <= end <= |s|
{
  forall i | 0 <= i < (end - start) / 2 :: s[start + i] == s[end - 1 - i]
}

ghost method CheckAllPalindromes(s: string, k: int, len: int)
  requires k > 0
  requires |s| % k == 0
  requires len == |s| / k
  ensures (forall j :: 0 <= j < k ==> IsPalSubrange(s, j * len, (j + 1) * len)) == 
           (forall j :: 0 <= j < k ==> isPalindrome(s[j * len..(j + 1) * len]))
{
}

lemma StringSliceIsPalindrome(s: string, start: int, end: int)
  requires 0 <= start <= end <= |s|
  ensures isPalindrome(s[start..end]) == IsPalSubrange(s, start, end)
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int) returns (result: string)
    requires k > 0
    ensures result == "YES" || result == "NO"
    ensures |s| % k != 0 ==> result == "NO"
    ensures |s| % k == 0 && (forall i :: 0 <= i < k ==> 
        isPalindrome(s[i * (|s| / k)..(i + 1) * (|s| / k)])) ==> result == "YES"
    ensures |s| % k == 0 && (exists i :: 0 <= i < k && 
        !isPalindrome(s[i * (|s| / k)..(i + 1) * (|s| / k)])) ==> result == "NO"
// </vc-spec>
// <vc-code>
{
  if |s| % k != 0 {
    result := "NO";
    return;
  }
  
  var len := |s| / k;
  var all_palindromes := true;
  var i := 0;
  
  while i < k
    invariant 0 <= i <= k
    invariant all_palindromes == (forall j :: 0 <= j < i ==> isPalindrome(s[j * len..(j + 1) * len]))
  {
    var substring := s[i * len..(i + 1) * len];
    if !isPalindrome(substring) {
      all_palindromes := false;
      break;
    }
    i := i + 1;
  }
  
  if all_palindromes {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

