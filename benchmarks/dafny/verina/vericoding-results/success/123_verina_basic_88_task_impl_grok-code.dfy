// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ToArray(xs: seq<int>) returns (result: array<int>)
    ensures
        result.Length == |xs| &&
        forall i :: 0 <= i < |xs| ==> result[i] == xs[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented while loop with invariant to verify postcondition by setting array elements correctly and handling empty sequence */
  result := new int[|xs|];
  var i := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant forall k :: 0 <= k < i ==> result[k] == xs[k]
  {
    result[i] := xs[i];
    i := i + 1;
  }
}
// </vc-code>
