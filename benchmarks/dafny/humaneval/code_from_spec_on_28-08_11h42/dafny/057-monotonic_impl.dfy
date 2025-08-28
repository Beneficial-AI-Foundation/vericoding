// <vc-helpers>
lemma MonotonicIncreasingHelper(xs: seq<int>, k: int)
  requires |xs| > 0
  requires 0 <= k < |xs| - 1
  requires forall i :: 0 <= i < k ==> xs[i] < xs[i+1]
  requires xs[k] >= xs[k+1]
  ensures !(forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j])
{
  assert xs[k] >= xs[k+1];
  assert 0 <= k < k+1 < |xs|;
  assert !(xs[k] < xs[k+1]);
}

lemma MonotonicDecreasingHelper(xs: seq<int>, k: int)
  requires |xs| > 0
  requires 0 <= k < |xs| - 1
  requires forall i :: 0 <= i < k ==> xs[i] > xs[i+1]
  requires xs[k] <= xs[k+1]
  ensures !(forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
{
  assert xs[k] <= xs[k+1];
  assert 0 <= k < k+1 < |xs|;
  assert !(xs[k] > xs[k+1]);
}

lemma StrictlyIncreasingImpliesMonotonic(xs: seq<int>)
  requires forall k :: 0 <= k < |xs| - 1 ==> xs[k] < xs[k+1]
  ensures forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]
{
  forall i, j | 0 <= i < j < |xs|
    ensures xs[i] < xs[j]
  {
    var k := i;
    while k < j - 1
      invariant i <= k < j
      invariant xs[i] < xs[k+1]
    {
      k := k + 1;
    }
  }
}

lemma StrictlyDecreasingImpliesMonotonic(xs: seq<int>)
  requires forall k :: 0 <= k < |xs| - 1 ==> xs[k] > xs[k+1]
  ensures forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j]
{
  forall i, j | 0 <= i < j < |xs|
    ensures xs[i] > xs[j]
  {
    var k := i;
    while k < j - 1
      invariant i <= k < j
      invariant xs[i] > xs[k+1]
    {
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
  if |xs| == 1 {
    return true;
  }
  
  var isIncreasing := true;
  var isDecreasing := true;
  var i := 0;
  
  while i < |xs| - 1 
    invariant 0 <= i <= |xs| - 1
    invariant isIncreasing ==> forall k :: 0 <= k < i ==> xs[k] < xs[k+1]
    invariant isDecreasing ==> forall k :: 0 <= k < i ==> xs[k] > xs[k+1]
    invariant !isIncreasing ==> exists k :: 0 <= k < i && xs[k] >= xs[k+1]
    invariant !isDecreasing ==> exists k :: 0 <= k < i && xs[k] <= xs[k+1]
  {
    if xs[i] >= xs[i+1] {
      if isIncreasing {
        MonotonicIncreasingHelper(xs, i);
      }
      isIncreasing := false;
    }
    if xs[i] <= xs[i+1] {
      if isDecreasing {
        MonotonicDecreasingHelper(xs, i);
      }
      isDecreasing := false;
    }
    i := i + 1;
  }
  
  if isIncreasing {
    StrictlyIncreasingImpliesMonotonic(xs);
  }
  if isDecreasing {
    StrictlyDecreasingImpliesMonotonic(xs);
  }
  
  result := isIncreasing || isDecreasing;
}
// </vc-code>
