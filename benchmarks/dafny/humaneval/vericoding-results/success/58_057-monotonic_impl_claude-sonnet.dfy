// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added helper functions to check monotonicity properties */
function IsIncreasing(xs: seq<int>): bool {
  forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]
}

function IsDecreasing(xs: seq<int>): bool {
  forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j]
}
// </vc-helpers>

// <vc-spec>
method monotonic(xs: seq<int>) returns (result: bool)

  requires |xs| > 0

  ensures result <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]) || (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed loop invariants and strengthened postcondition proof */
{
  var increasing := true;
  var decreasing := true;
  
  var i := 0;
  while i < |xs| - 1
    invariant 0 <= i <= |xs| - 1
    invariant increasing ==> (forall k, l :: 0 <= k < l < i + 1 ==> xs[k] < xs[l])
    invariant decreasing ==> (forall k, l :: 0 <= k < l < i + 1 ==> xs[k] > xs[l])
    invariant !increasing ==> (exists k :: 0 <= k < i && xs[k] >= xs[k + 1])
    invariant !decreasing ==> (exists k :: 0 <= k < i && xs[k] <= xs[k + 1])
  {
    if xs[i] >= xs[i + 1] {
      increasing := false;
    }
    if xs[i] <= xs[i + 1] {
      decreasing := false;
    }
    i := i + 1;
  }
  
  result := increasing || decreasing;
}
// </vc-code>
