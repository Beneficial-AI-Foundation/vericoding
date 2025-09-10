function isPalindrome(s: string): bool
{
    forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}

// <vc-helpers>
// no helpers needed
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
  var len := |s|;
  if len % k != 0 {
    return "NO";
  }
  var m := len / k;
  // from division properties: len == k*m + len%k, and len%k == 0, so k*m == len
  assert len == k * m + len % k;
  assert len % k == 0;
  assert k * m == len;

  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant forall j :: 0 <= j < i ==> isPalindrome(s[j * m .. (j + 1) * m])
  {
    if !isPalindrome(s[i * m .. (i + 1) * m]) {
      return "NO";
    }
    i := i + 1;
  }
  return "YES";
}
// </vc-code>

