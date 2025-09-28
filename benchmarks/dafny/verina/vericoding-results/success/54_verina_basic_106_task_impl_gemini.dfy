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
  /* code modified by LLM (iteration 2): used a while loop to fix index-out-of-range error */
  var i: nat := 0;
  result := [];
  while i < |a|
    invariant |result| == i
    invariant i <= |a|
    invariant |a| == |b|
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] + b[k]
  {
    result := result + [a[i] + b[i]];
    i := i + 1;
  }
}
// </vc-code>
