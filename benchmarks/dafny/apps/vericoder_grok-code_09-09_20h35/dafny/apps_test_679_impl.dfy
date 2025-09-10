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
// No changes needed
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
  result := "No";
  if |s| >= 3 {
    var i := 0;
    while i <= |s| - 3
      invariant |s| >= 3
      invariant 0 <= i
      invariant result == "No"
      invariant forall k :: 0 <= k < i ==> !HasAllThreeColors(s, k)
      decreases |s| - 3 - i
    {
      if HasAllThreeColors(s, i) {
        result := "Yes";
        i := |s|;
      } else {
        i := i + 1;
      }
    }
  }
}
// </vc-code>

