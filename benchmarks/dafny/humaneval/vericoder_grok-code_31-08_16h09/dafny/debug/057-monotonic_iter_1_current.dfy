

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method monotonic(xs: seq<int>) returns (result: bool)
  // pre-conditions-start
  requires |xs| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]) || (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |xs| == 1 {
    result := true;
  } else {
    var increasing := true;
    var decreasing := true;
    for i := 0 to |xs| - 2
      invariant 0 <= i <= |xs| - 1
      invariant increasing ==> (forall k:: 0 <= k < i ==> xs[k] < xs[k+1])
      invariant decreasing ==> (forall k:: 0 <= k < i ==> xs[k] > xs[k+1])
    {
      if xs[i] >= xs[i + 1] {
        increasing := false;
      }
      if xs[i] <= xs[i + 1] {
        decreasing := false;
      }
    }
    result := increasing || decreasing;
  }
}
// </vc-code>

