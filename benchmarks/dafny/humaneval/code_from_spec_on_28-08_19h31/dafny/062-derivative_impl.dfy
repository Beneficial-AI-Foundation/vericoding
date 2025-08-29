// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method derivative(xs: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |xs| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |xs| - 1
  ensures forall i :: 0 <= i < |result| ==> result[i] == xs[i+1] * (i+1)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  result := [];
  for i := 0 to |xs| - 1
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == xs[k+1] * (k+1)
  {
    result := result + [xs[i+1] * (i+1)];
  }
}
// </vc-code>
