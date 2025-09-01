

// <vc-helpers>
lemma IsIncreasingTransitive(xs: seq<int>, i: int, j: int, k: int)
  requires 0 <= i < j < k < |xs|
  requires forall a, b :: 0 <= a < b < j ==> xs[a] < xs[b]
  requires xs[i] < xs[j] && xs[j] < xs[k]
  ensures xs[i] < xs[k]
{
}

lemma IsDecreasingTransitive(xs: seq<int>, i: int, j: int, k: int)
  requires 0 <= i < j < k < |xs|
  requires forall a, b :: 0 <= a < b < j ==> xs[a] > xs[b]
  requires xs[i] > xs[j] && xs[j] > xs[k]
  ensures xs[i] > xs[k]
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
  if |xs| == 1 {
    return true;
  }
  
  var isIncreasing := true;
  var isDecreasing := true;
  
  var i := 0;
  while i < |xs| - 1
    invariant 0 <= i <= |xs| - 1
    invariant isIncreasing ==> (forall a, b :: 0 <= a < b <= i ==> xs[a] < xs[b])
    invariant isDecreasing ==> (forall a, b :: 0 <= a < b <= i ==> xs[a] > xs[b])
    invariant !isIncreasing ==> exists a, b :: 0 <= a < b <= i && xs[a] >= xs[b]
    invariant !isDecreasing ==> exists a, b :: 0 <= a < b <= i && xs[a] <= xs[b]
  {
    if xs[i] >= xs[i + 1] {
      isIncreasing := false;
    }
    if xs[i] <= xs[i + 1] {
      isDecreasing := false;
    }
    i := i + 1;
  }
  
  result := isIncreasing || isDecreasing;
}
// </vc-code>

