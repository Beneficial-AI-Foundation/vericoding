// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no helpers needed */

// </vc-helpers>

// <vc-spec>
method derivative(xs: seq<int>) returns (result: seq<int>)

  requires |xs| > 0

  ensures |result| == |xs| - 1
  ensures forall i :: 0 <= i < |result| ==> result[i] == xs[i+1] * (i+1)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): switched to a while loop to avoid a compiler index-out-of-range error with the seq constructor */
  result := [];
  var i := 0;
  while i < |xs| - 1
    invariant 0 <= i <= |xs| - 1
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == xs[j+1] * (j+1)
  {
    result := result + [xs[i+1] * (i+1)];
    i := i + 1;
  }
}
// </vc-code>
