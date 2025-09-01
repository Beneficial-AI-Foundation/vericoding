

// <vc-helpers>
lemma IsMonotonicIncreasing(xs: seq<int>)
  requires |xs| > 0
  ensures (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]) ==> 
          (forall i :: 0 <= i < |xs| - 1 ==> xs[i] < xs[i + 1])
{
}

lemma IsMonotonicDecreasing(xs: seq<int>)
  requires |xs| > 0
  ensures (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j]) ==> 
          (forall i :: 0 <= i < |xs| - 1 ==> xs[i] > xs[i + 1])
{
}

lemma AdjacentImpliesFullIncreasing(xs: seq<int>)
  requires |xs| > 0
  ensures (forall i :: 0 <= i < |xs| - 1 ==> xs[i] < xs[i + 1]) ==> 
          (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j])
{
}

lemma AdjacentImpliesFullDecreasing(xs: seq<int>)
  requires |xs| > 0
  ensures (forall i :: 0 <= i < |xs| - 1 ==> xs[i] > xs[i + 1]) ==> 
          (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
{
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
    invariant increasing == (forall k :: 0 <= k < i ==> (k < |xs| - 1 ==> xs[k] < xs[k + 1]))
    invariant decreasing == (forall k :: 0 <= k < i ==> (k < |xs| - 1 ==> xs[k] > xs[k + 1]))
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
  
  result := increasing || decreasing;
}
// </vc-code>

