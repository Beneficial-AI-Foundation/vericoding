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
    return "NO";
  }
  var m := |s| / k;
  assert |s| == k * (|s| / k) + |s| % k;
  assert |s| % k == 0;
  assert k * m == |s|;
  assert 0 <= m;

  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant 0 <= m
    invariant k * m == |s|
    invariant forall j :: 0 <= j < i ==> 0 <= j * m && (j + 1) * m <= |s| && isPalindrome(s[j * m .. (j + 1) * m])
    decreases k - i
  {
    assert 0 <= i * m;
    assert i + 1 <= k;
    assert (i + 1) * m <= |s|;

    if !isPalindrome(s[i * m .. (i + 1) * m]) {
      return "NO";
    }
    assert isPalindrome(s[i * m .. (i + 1) * m]);

    forall j | 0 <= j < i + 1
      ensures 0 <= j * m && (j + 1) * m <= |s| && isPalindrome(s[j * m .. (j + 1) * m])
    {
      if j < i {
        assert 0 <= j < i;
        assert 0 <= j * m && (j + 1) * m <= |s| && isPalindrome(s[j * m .. (j + 1) * m]);
      } else {
        assert j == i;
        assert 0 <= i * m;
        assert (i + 1) * m <= |s|;
        assert isPalindrome(s[i * m .. (i + 1) * m]);
      }
    }

    i := i + 1;
  }
  return "YES";
}
// </vc-code>

