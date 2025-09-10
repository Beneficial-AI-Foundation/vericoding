function isPalindrome(s: string): bool
{
    forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}

// <vc-helpers>
lemma PairwiseImpliesIsPalindrome(s: string, a: int, m: int)
  requires 0 <= a && m >= 0 && a + m <= |s|
  requires forall t :: 0 <= t < m/2 ==> s[a + t] == s[a + m - 1 - t]
  ensures isPalindrome(s[a .. a + m])
{
  assert |s[a .. a + m]| == m;
  assert (forall i :: 0 <= i < |s[a .. a + m]|/2 ==>
            (s[a .. a + m])[i] == (s[a .. a + m])[|s[a .. a + m]| - 1 - i]);
  {
    fix i;
    assume 0 <= i < |s[a .. a + m]|/2;
    assert 0 <= i < m/2;
    assert (s[a .. a + m])[i] == s[a + i];
    assert (s[a .. a + m])[m - 1 - i] == s[a + m - 1 - i];
    assert s[a + i] == s[a + m - 1 - i];
  }
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

  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant forall j :: 0 <= j < i ==>
      forall t :: 0 <= t < m/2 ==> s[j * m + t] == s[(j + 1) * m - 1 - t]
    decreases k - i
  {
    var t := 0;
    while t < m/2
      invariant 0 <= t <= m/2
      invariant forall j :: 0 <= j < i ==>
        forall u :: 0 <= u < m/2 ==> s[j * m + u] == s[(j + 1) * m - 1 - u]
      invariant forall u :: 0 <= u < t ==> s[i * m + u] == s[(i + 1) * m - 1 - u]
      decreases m/2 - t
    {
      if s[i * m + t] != s[(i + 1) * m - 1 - t] {
        return "NO";
      }
      t := t + 1;
    }
    i := i + 1;
  }

  var j := 0;
  while j < k
    decreases k - j
  {
    PairwiseImpliesIsPalindrome(s, j * m, m);
    j := j + 1;
  }
  return "YES";
}
// </vc-code>

