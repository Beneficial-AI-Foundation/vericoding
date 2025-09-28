// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method BitwiseAnd(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == (a[i] & b[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added bounds invariant to fix index out of range */
  var i: int := 0;
  result := [];
  while i < |a|
    invariant |result| == i
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> result[j] == (a[j] & b[j])
  {
    result := result + [a[i] & b[i]];
    i := i + 1;
  }
}
// </vc-code>
