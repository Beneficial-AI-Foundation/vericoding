// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
method ToArray_Helper(xs: seq<int>) returns (result: array<int>)
    ensures
        result.Length == |xs| &&
        forall i :: 0 <= i < |xs| ==> result[i] == xs[i]
{
    result := new int[|xs|];
    var idx := 0;
    while idx < |xs|
        invariant 0 <= idx <= |xs|
        invariant forall j :: 0 <= j < idx ==> result[j] == xs[j]
    {
        result[idx] := xs[idx];
        idx := idx + 1;
    }
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
  /* code modified by LLM (iteration 2): Call renamed helper method */
  result := ToArray_Helper(xs);
}
// </vc-code>
