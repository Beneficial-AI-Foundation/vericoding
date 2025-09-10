predicate ValidInput(s: string)
{
    |s| >= 0 && forall i :: 0 <= i < |s| ==> s[i] in {'A', 'B', 'C', '.'}
}

predicate HasAllThreeColors(s: string, start: int)
    requires 0 <= start <= |s| - 3
{
    'A' in s[start..start+3] && 'B' in s[start..start+3] && 'C' in s[start..start+3]
}

predicate PossibleToGetAllColors(s: string)
{
    |s| >= 3 && exists i :: 0 <= i <= |s| - 3 && HasAllThreeColors(s, i)
}

// <vc-helpers>
// (no helper lemmas needed)
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == "Yes" ==> PossibleToGetAllColors(s)
    ensures result == "No" ==> !PossibleToGetAllColors(s)
    ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  if n < 3 {
    result := "No";
    return;
  }
  var i := 0;
  while i <= n - 3
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i && j <= n - 3 ==> !HasAllThreeColors(s, j)
    decreases n - i
  {
    if ('A' in s[i..i+3] && 'B' in s[i..i+3] && 'C' in s[i..i+3]) {
      assert HasAllThreeColors(s, i);
      result := "Yes";
      return;
    }
    // From the negation and the loop condition we can conclude !HasAllThreeColors(s,i)
    assert !( 'A' in s[i..i+3] && 'B' in s[i..i+3] && 'C' in s[i..i+3]);
    assert i <= n - 3;
    assert !HasAllThreeColors(s, i);
    i := i + 1;
  }
  // After the loop, for n >= 3 every start position 0..n-3 has been checked and none have all three colors
  if n >= 3 {
    assert i > n - 3;
    assert forall j :: 0 <= j <= n - 3 ==> !HasAllThreeColors(s, j);
  }
  result := "No";
}
// </vc-code>

