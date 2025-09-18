// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] + b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Replaced direct sequence construction with a while loop to resolve index out of range compilation error. */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |a| == |b|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] + b[k]
  {
    result := result + [a[i] + b[i]];
    i := i + 1;
  }
}
// </vc-code>
