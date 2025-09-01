

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
  result := [ xs[i+1] * (i+1) for i in [0..(|xs|-2)] ];
}
// </vc-code>

