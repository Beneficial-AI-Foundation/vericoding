// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide SeqLength to return sequence length */
function SeqLength(xs: seq<int>): int { |xs| }
// </vc-helpers>

// <vc-spec>
method ToArray(xs: seq<int>) returns (result: array<int>)
    ensures
        result.Length == |xs| &&
        forall i :: 0 <= i < |xs| ==> result[i] == xs[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement ToArray with proper invariants without nullable check */
  result := new int[|xs|];
  var i := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant result.Length == |xs|
    invariant forall j :: 0 <= j < i ==> result[j] == xs[j]
    decreases |xs| - i
  {
    result[i] := xs[i];
    i := i + 1;
  }
}

// </vc-code>
