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
/* code modified by LLM (iteration 2): added loop invariant to prove postcondition */
{
  result := new int[|xs|];
  for i := 0 to |xs|
    invariant 0 <= i <= |xs|
    invariant forall j :: 0 <= j < i ==> result[j] == xs[j]
  {
    result[i] := xs[i];
  }
}
// </vc-code>
