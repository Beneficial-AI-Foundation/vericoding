

// <vc-helpers>
lemma ConsecutiveIncreasingImpliesTotal(xs: seq<int>)
  requires |xs| >= 2
  ensures (forall i : int :: 0 <= i < |xs| - 1 ==> xs[i] < xs[i+1]) ==> (forall i, j : int :: 0 <= i < j < |xs| ==> xs[i] < xs[j])
{
  var i := 0;
  var j := |xs| - 1;
  // Prove for all i < j
  assert (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]) by {
    var i0 := 0;
    for i0 := 0 to |xs| - 1
      invariant 0 <= i0 < |xs|
    {
      var j0 := i0 + 1;
      while j0 < |xs|
        invariant i0 < j0 <= |xs|
        invariant xs[i0] < xs[j0]
      {
        assert xs[j0-1] < xs[j0];
        assert xs[i0] < xs[j0];
        j0 := j0 + 1;
      }
    }
  };
}

lemma ConsecutiveDecreasingImpliesTotal(xs: seq<int>)
  requires |xs| >= 2
  ensures (forall i : int :: 0 <= i < |xs| - 1 ==> xs[i] > xs[i+1]) ==> (forall i, j : int :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
{
  var i := 0;
  var j := |xs| - 1;
  assert (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j]) by {
    var i0 := 0;
    for i0 := 0 to |xs| - 1
      invariant 0 <= i0 < |xs|
    {
      var j0 := i0 + 1;
      while j0 < |xs|
        invariant i0 < j0 <= |xs|
        invariant xs[i0] > xs[j0]
      {
        assert xs[j0-1] > xs[j0];
        assert xs[i0] > xs[j0];
        j0 := j0 + 1;
      }
    }
  };
}
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
{return (forall i : int :: 0 <= i < |xs| - 1 ==> xs[i] < xs[i+1]) || (forall i : int :: 0 <= i < |xs| - 1 ==> xs[i] > xs[i+1]);}
// </vc-code>

