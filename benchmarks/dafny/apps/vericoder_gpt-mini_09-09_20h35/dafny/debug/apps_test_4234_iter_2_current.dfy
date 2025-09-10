predicate ValidInput(n: int, s: string)
{
    n == |s| && n >= 0
}

predicate IsGoodString(s: string)
{
    |s| % 2 == 0 && forall i :: 0 <= i < |s|/2 ==> s[2*i] != s[2*i+1]
}

// <vc-helpers>
// No helper code required for this proof.
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (deletedCount: int, result: string)
    requires ValidInput(n, s)
    ensures deletedCount >= 0
    ensures deletedCount == |s| - |result|
    ensures IsGoodString(result)
    ensures deletedCount + |result| == |s|
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var res := "";
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= |res| <= n
    invariant forall k :: 0 <= k < |res|/2 ==> res[2*k] != res[2*k+1]
  {
    if |res| % 2 == 0 {
      // start a new pair with s[i]
      res := res + s[i..i+1];
    } else {
      // attempt to complete the current pair only if different
      if |res| > 0 && res[|res|-1] != s[i] {
        res := res + s[i..i+1];
      } else {
        // skip s[i]
      }
    }
    i := i + 1;
  }
  // If there's an unmatched character at the end, drop it to ensure even length
  if |res| % 2 == 1 {
    res := res[..|res|-1];
  }
  deletedCount := n - |res|;
  result := res;
}
// </vc-code>

