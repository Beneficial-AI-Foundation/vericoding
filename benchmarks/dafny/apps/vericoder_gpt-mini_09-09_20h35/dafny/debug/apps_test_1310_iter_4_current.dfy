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
predicate ValidInput(arr: seq<bv32>)
{
    |arr| > 0
}

predicate IsMaxXorSubarray(arr: seq<bv32>, result: bv32)
    requires ValidInput(arr)
{
    (exists i, j ::
        0 <= i <= j < |arr| &&
        result == XorRange(arr, i, j)
    ) &&
    (forall i1, j1 ::
        0 <= i1 <= j1 < |arr| ==>
        (XorRange(arr, i1, j1) as int) <= (result as int)
    )
}

function XorRange(arr: seq<bv32>, i: int, j: int): bv32
  requires 0 <= i <= j < |arr|
  decreases j - i
{
  if i == j then arr[i] else arr[i] ^ XorRange(arr, i+1, j)
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
  // initialize result and witness indices
  result := arr[0];
  var bi := 0;
  var bj := 0;

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= bi <= bj < n
    invariant result == XorRange(arr, bi, bj)
    invariant forall i1, j1 :: 0 <= i1 <= j1 < n && i1 < i ==> (XorRange(arr, i1, j1) as int) <= (result as int)
    decreases n - i
  {
    var cur := arr[i];
    var j := i;
    while j < n
      invariant i <= j <= n
      invariant j < n ==> cur == XorRange(arr, i, j)
      invariant 0 <= bi <= bj < n
      invariant result == XorRange(arr, bi, bj)
      invariant forall i1, j1 :: 0 <= i1 <= j1 < n && (i1 < i || (i1 == i && j1 < j)) ==> (XorRange(arr, i1, j1) as int) <= (result as int)
      decreases n - j
    {
      // j < n holds at loop entry, so cur == XorRange(arr,i,j) holds
      if (cur as int) > (result as int) {
        result := cur;
        bi := i;
        bj := j;
      }
      if j + 1 < n {
        // extend current range [i..j] to [i..j+1] by direct function call
        cur := XorRange(arr, i, j+1);
        j := j + 1;
        assert cur == XorRange(arr, i, j);
      } else {
        break;
      }
    }
    i := i + 1;
  }

  // at this point result == XorRange(arr,bi,bj) and by invariants it's >= all subarray xors
  return;
}
// </vc-code>

