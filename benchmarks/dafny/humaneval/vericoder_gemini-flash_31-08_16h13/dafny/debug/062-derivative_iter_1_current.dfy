

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
    var n := |xs|;
    var res_seq := new int[n - 1];
    for i := 0 to n - 2
        invariant 0 <= i <= n - 1
        invariant forall j :: 0 <= j < i ==> res_seq[j] == xs[j+1] * (j+1)
    {
        res_seq[i] := xs[i+1] * (i+1);
    }
    return res_seq;
}
// </vc-code>

