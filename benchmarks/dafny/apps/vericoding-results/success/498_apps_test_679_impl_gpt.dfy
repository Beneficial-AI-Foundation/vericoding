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
    assert !PossibleToGetAllColors(s);
    return;
  }

  var i := 0;
  while i <= n - 3
    invariant 0 <= i <= n - 2
    invariant n == |s|
    invariant forall j :: 0 <= j < i ==> !HasAllThreeColors(s, j)
    decreases n - 2 - i
  {
    if HasAllThreeColors(s, i) {
      assert 0 <= i <= |s| - 3;
      assert HasAllThreeColors(s, i);
      assert |s| >= 3;
      assert exists j :: 0 <= j <= |s| - 3 && HasAllThreeColors(s, j);
      assert PossibleToGetAllColors(s);
      result := "Yes";
      return;
    }
    i := i + 1;
  }

  assert i >= n - 2;
  assert i <= n - 2;
  assert i == n - 2;

  assert forall j :: 0 <= j <= |s| - 3 ==> !HasAllThreeColors(s, j) by {
    forall j | 0 <= j <= |s| - 3
      ensures !HasAllThreeColors(s, j)
    {
      assert n == |s|;
      assert j <= n - 3;
      assert i == n - 2;
      assert j < i;
      assert 0 <= j < i;
      assert forall k :: 0 <= k < i ==> !HasAllThreeColors(s, k);
      assert !HasAllThreeColors(s, j);
    }
  }

  assert |s| >= 3;
  assert !(exists j :: 0 <= j <= |s| - 3 && HasAllThreeColors(s, j));
  assert !PossibleToGetAllColors(s);

  result := "No";
}
// </vc-code>

