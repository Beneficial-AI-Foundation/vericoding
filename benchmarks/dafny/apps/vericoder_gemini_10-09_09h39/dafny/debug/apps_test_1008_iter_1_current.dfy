function isPalindrome(s: string): bool
{
    forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}

// <vc-helpers>

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
  
  var n := |s| / k;
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant |s| % k == 0
    invariant n == |s| / k
    invariant forall j :: 0 <= j < i ==> isPalindrome(s[j * n .. (j + 1) * n])
  {
    var sub := s[i * n .. (i + 1) * n];
    if !isPalindrome(sub) {
      result := "NO";
      return;
    }
    i := i + 1;
  }
  
  result := "YES";
}
// </vc-code>

