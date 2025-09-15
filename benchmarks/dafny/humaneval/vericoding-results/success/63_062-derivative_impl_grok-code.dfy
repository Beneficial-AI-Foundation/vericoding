// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method derivative(xs: seq<int>) returns (result: seq<int>)

  requires |xs| > 0

  ensures |result| == |xs| - 1
  ensures forall i :: 0 <= i < |result| ==> result[i] == xs[i+1] * (i+1)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): used an array with a while loop and invariant to compute the derivative coefficients and verify the postconditions */
  var n := |xs| - 1;
  var temp := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> temp[j] == xs[j + 1] * (j + 1)
  {
    temp[i] := xs[i + 1] * (i + 1);
    i := i + 1;
  }
  result := temp[..];
}
// </vc-code>
