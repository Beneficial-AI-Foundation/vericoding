

// <vc-helpers>
lemma AdjacentImpliesFullIncreasing(xs: seq<int>)
  requires |xs| > 0
  ensures (forall i :: 0 <= i < |xs| - 1 ==> xs[i] < xs[i + 1]) ==> 
          (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j])
{
  if forall i :: 0 <= i < |xs| - 1 ==> xs[i] < xs[i + 1] {
    var k := 0;
    while k < |xs| - 1
      invariant 0 <= k <= |xs| - 1
      invariant forall i, j :: 0 <= i <= k < j < |xs| ==> xs[i] < xs[j]
    {
      // Prove that xs[k] < xs[j] for all j > k
      var j := k + 1;
      while j < |xs|
        invariant k + 1 <= j <= |xs|
        invariant forall m :: k < m < j ==> xs[k] < xs[m]
      {
        // By transitivity: xs[k] < xs[k+1] < ... < xs[j]
        // Since adjacent elements are increasing, xs[k] < xs[j]
        j := j + 1;
      }
      k := k + 1;
    }
  }
}

lemma AdjacentImpliesFullDecreasing(xs: seq<int>)
  requires |xs| > 0
  ensures (forall i :: 0 <= i < |xs| - 1 ==> xs[i] > xs[i + 1]) ==> 
          (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
{
  if forall i :: 0 <= i < |xs| - 1 ==> xs[i] > xs[i + 1] {
    var k := 0;
    while k < |xs| - 1
      invariant 0 <= k <= |xs| - 1
      invariant forall i, j :: 0 <= i <= k < j < |xs| ==> xs[i] > xs[j]
    {
      // Prove that xs[k] > xs[j] for all j > k
      var j := k + 1;
      while j < |xs|
        invariant k + 1 <= j <= |xs|
        invariant forall m :: k < m < j ==> xs[k] > xs[m]
      {
        // By transitivity: xs[k] > xs[k+1] > ... > xs[j]
        // Since adjacent elements are decreasing, xs[k] > xs[j]
        j := j + 1;
      }
      k := k + 1;
    }
  }
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
{
  var increasing := true;
  var decreasing := true;
  
  var i := 0;
  while i < |xs| - 1
    invariant 0 <= i <= |xs| - 1
    invariant increasing ==> (forall k :: 0 <= k < i ==> xs[k] < xs[k + 1])
    invariant decreasing ==> (forall k :: 0 <= k < i ==> xs[k] > xs[k + 1])
    invariant !increasing ==> (exists k :: 0 <= k < i && xs[k] >= xs[k + 1])
    invariant !decreasing ==> (exists k :: 0 <= k < i && xs[k] <= xs[k + 1])
  {
    if xs[i] < xs[i + 1] {
      decreasing := false;
    } else if xs[i] > xs[i + 1] {
      increasing := false;
    } else {
      increasing := false;
      decreasing := false;
    }
    i := i + 1;
  }
  
  if increasing {
    AdjacentImpliesFullIncreasing(xs);
    assert forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j];
  } else if decreasing {
    AdjacentImpliesFullDecreasing(xs);
    assert forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j];
  }
  result := increasing || decreasing;
}
// </vc-code>

