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

function method IsPalSubrange(s: string, start: int, end: int): bool
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
    invariant all_palindromes == (forall j :: 0 <= j < i ==> IsPalSubrange(s, j * len, (j + 1) * len))
  {
    var start := i * len;
    var end := (i + 1) * len;
    assert start >= 0 && end <= |s| && start <= end;
    
    var is_pal := true;
    var idx := 0;
    
    while idx < len / 2
      invariant 0 <= idx <= len/2
      invariant is_pal ==> (forall p :: 0 <= p < idx ==> s[start + p] == s[end - 1 - p])
      invariant !is_pal ==> exists p :: 0 <= p < idx && s[start + p] != s[end - 1 - p]
    {
      if s[start + idx] != s[end - 1 - idx] {
        is_pal := false;
        break;
      }
      idx := idx + 1;
    }
    
    if !is_pal {
      all_palindromes := false;
      break;
    }
    i := i + 1;
  }
  
  // Apply the helper lemma to connect our internal representation with the specification
  CheckAllPalindromes(s, k, len);
  
  if all_palindromes {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

