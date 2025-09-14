predicate ValidInput(arr: seq<bv32>)
{
    |arr| > 0
}

predicate IsMaxXorSubarray(arr: seq<bv32>, result: bv32)
    requires ValidInput(arr)
{
    exists i, j :: 0 <= i <= j < |arr| && result == XorRange(arr, i, j) &&
    forall i1, j1 :: 0 <= i1 <= j1 < |arr| ==> 
        (XorRange(arr, i1, j1) as int) <= (result as int)
}

// <vc-helpers>
function XorRange(arr: seq<bv32>, i: int, j: int): bv32
  requires 0 <= i <= j < |arr|
  decreases j - i
{
  if i == j then arr[i] else XorRange(arr, i, j - 1) ^ arr[j]
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<bv32>) returns (result: bv32)
    requires ValidInput(arr)
    ensures IsMaxXorSubarray(arr, result)
// </vc-spec>
// <vc-code>
{
  var n := |arr|;
  var best: bv32 := arr[0];
  var bestI := 0;
  var bestJ := 0;

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= bestI <= bestJ < n
    invariant best == XorRange(arr, bestI, bestJ)
    invariant forall ii:int, jj:int :: 0 <= ii < i && ii <= jj < n ==> (XorRange(arr, ii, jj) as int) <= (best as int)
    decreases n - i
  {
    var bestStart := best;
    var j := i;
    while j < n
      invariant i <= j <= n
      invariant 0 <= bestI <= bestJ < n
      invariant best == XorRange(arr, bestI, bestJ)
      invariant forall jj:int :: i <= jj < j ==> (XorRange(arr, i, jj) as int) <= (best as int)
      invariant forall ii:int, jj:int :: 0 <= ii < i && ii <= jj < n ==> (XorRange(arr, ii, jj) as int) <= (bestStart as int)
      invariant (bestStart as int) <= (best as int)
      decreases n - j
    {
      var candidate := XorRange(arr, i, j);
      if (candidate as int) > (best as int) {
        best := candidate;
        bestI := i;
        bestJ := j;
      }
      assert (XorRange(arr, i, j) as int) <= (best as int);
      j := j + 1;
    }
    assert j == n;
    assert forall jj:int :: i <= jj < n ==> (XorRange(arr, i, jj) as int) <= (best as int) by {
      forall jj:int | i <= jj < n
        ensures (XorRange(arr, i, jj) as int) <= (best as int)
      {
        assert j == n;
// </vc-code>

