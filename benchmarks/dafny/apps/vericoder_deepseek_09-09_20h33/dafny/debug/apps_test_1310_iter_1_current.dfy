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
{
  if i == j then arr[i]
  else XorRange(arr, i, j - 1) ^ arr[j]
}

lemma XorRangeProperties(arr: seq<bv32>)
  requires ValidInput(arr)
  ensures forall i, j :: 0 <= i <= j < |arr| ==> XorRange(arr, i, j) as int >= 0
{
}

lemma MaxXorExists(arr: seq<bv32>)
  requires ValidInput(arr)
  ensures exists result: bv32 :: IsMaxXorSubarray(arr, result)
{
  var max_val := 0 as bv32;
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant exists k, l :: 0 <= k <= l < i ==> XorRange(arr, k, l) as int <= (max_val as int)
  {
    var current := 0 as bv32;
    var j := i;
    while j < |arr|
      invariant i <= j <= |arr|
      invariant current == XorRange(arr, i, j - 1)
    {
      current := current ^ arr[j];
      if current as int > max_val as int {
        max_val := current;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<bv32>) returns (result: bv32)
    requires ValidInput(arr)
    ensures IsMaxXorSubarray(arr, result)
// </vc-spec>
// <vc-code>
{
  XorRangeProperties(arr);
  MaxXorExists(arr);
  
  var max_result := 0 as bv32;
  var n := |arr|;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant exists k, l :: 0 <= k <= l < i ==> XorRange(arr, k, l) as int <= (max_result as int)
  {
    var current_xor := 0 as bv32;
    var j := i;
    
    while j < n
      invariant i <= j <= n
      invariant current_xor == XorRange(arr, i, j - 1)
      invariant forall k :: i <= k < j ==> XorRange(arr, i, k) as int <= (max_result as int)
    {
      current_xor := current_xor ^ arr[j];
      if (current_xor as int) > (max_result as int) {
        max_result := current_xor;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := max_result;
}
// </vc-code>

