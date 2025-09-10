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
function method XorRange(arr: seq<bv32>, i: int, j: int): bv32
  requires 0 <= i <= j < |arr|
  decreases j - i
{
  if i == j then arr[i] else XorRange(arr, i, j - 1) + arr[j]
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
  var best := XorRange(arr, 0, 0);
  var bi := 0;
  var bj := 0;

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= bi <= bj < n
    invariant best == XorRange(arr, bi, bj)
    invariant forall i1, j1 :: 0 <= i1 < i && i1 <= j1 < n ==> (XorRange(arr, i1, j1) as int) <= (best as int)
    decreases n - i
  {
    var j := i;
    while j < n
      invariant i <= j <= n
      invariant 0 <= bi <= bj < n
      invariant best == XorRange(arr, bi, bj)
      invariant forall j1 :: i <= j1 < j ==> (XorRange(arr, i, j1) as int) <= (best as int)
      invariant forall i1, j1 :: 0 <= i1 < i && i1 <= j1 < n ==> (XorRange(arr, i1, j1) as int) <= (best as int)
      decreases n - j
    {
      if (XorRange(arr, i, j) as int) > (best as int) {
        best := XorRange(arr, i, j);
        bi := i;
        bj := j;
      }
      assert (XorRange(arr, i, j) as int) <= (best as int);
      j := j + 1;
    }
    i := i + 1;
  }

  result := best;
}
// </vc-code>

