predicate ValidInput(n: int, s: string)
{
    n == |s| && n >= 0
}

predicate IsGoodString(s: string)
{
    |s| % 2 == 0 && forall i :: 0 <= i < |s|/2 ==> s[2*i] != s[2*i+1]
}

// <vc-helpers>
predicate ValidStk(stk: seq<char>)
{
  forall i :: 0 <= i < |stk| / 2 ==> stk[2*i] != stk[2*i+1]
}
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
  var stk: seq<char> := [];
  for i: int := 0; i < n; i := i + 1
    invariant ValidStk(stk)
    invariant |stk| <= i + 1
    invariant 0 <= i <= n && |stk| >= 0
  {
    if |stk| % 2 == 0 {
      if |stk| == 0 || s[i] != stk[|stk|-1] {
        stk := stk + [s[i]];
      }
    } else if s[i] != stk[|stk|-1] {
      stk := stk + [s[i]];
    }
  }
  if |stk| % 2 == 1 {
    stk := stk[..|stk|-1];
  }
  assert |stk| % 2 == 0;
  result := stk;
  deletedCount := |s| - |stk|;
}
// </vc-code>

