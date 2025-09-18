// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ArrayElementMatch(a: array<int>, s: seq<int>, i: int): bool
  requires 0 <= i < a.Length && a.Length == |s|
  reads a
{
  a[i] == s[i]
}
// </vc-helpers>

// <vc-spec>
method ToArray(xs: seq<int>) returns (result: array<int>)
    ensures
        result.Length == |xs| &&
        forall i :: 0 <= i < |xs| ==> result[i] == xs[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Added reads clause to function call */
  result := new int[|xs|];
  var idx: int := 0;
  while idx < |xs|
    invariant 0 <= idx <= |xs|
    invariant forall j :: 0 <= j < idx ==> result[j] == xs[j]
  {
    result[idx] := xs[idx];
    idx := idx + 1;
  }
}
// </vc-code>
