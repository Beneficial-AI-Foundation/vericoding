function isPalindrome(s: string): bool
{
    forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}

// <vc-helpers>
lemma DivMul(len:int, k:int)
  requires k > 0
  requires len >= 0
  requires len % k == 0
  ensures (len / k) * k == len
{
  assert len == (len / k) * k + len % k;
  assert len % k == 0;
  assert len == (len / k) * k;
}

lemma DivNonneg(len:int, k:int)
  requires k > 0
  requires len >= 0
  ensures len / k >= 0
{
  assert len / k >= 0;
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
  var len := |s|;
  if len % k != 0 {
    return "NO";
  }
  var m := len / k;
  DivMul(len, k);
  DivNonneg(len, k);
  assert m * k == len;
  assert m >= 0;

  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant forall j :: 0 <= j < i ==> isPalindrome(s[j * m .. (j + 1) * m])
    invariant m * k == len
    invariant m >= 0
    decreases k - i
  {
    if !isPalindrome(s[i * m .. (i + 1) * m]) {
      return "NO";
    }
    i := i + 1;
  }
  return "YES";
}
// </vc-code>

