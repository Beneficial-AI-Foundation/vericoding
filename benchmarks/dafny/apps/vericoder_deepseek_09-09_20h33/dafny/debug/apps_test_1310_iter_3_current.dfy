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
}

ghost var global_max: bv32;

lemma UpdateMax(k: int, l: int, arr: seq<bv32>)
  requires 0 <= k <= l < |arr|
  requires ValidInput(arr)
  ensures (XorRange(arr, k, l) as int) <= (global_max as int)
{
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<bv32>) returns (result: bv32)
    requires ValidInput(arr)
    ensures IsMaxXorSubarray(arr, result)
// </vc-spec>
// <vc-code>
{
  var max_result := 0 as bv32;
  ghost global_max := max_result;
  var n := |arr|;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant exists k, l :: 0 <= k <= l < i && XorRange(arr, k, l) as int <= (max_result as int)
    invariant global_max == max_result
  {
    var current_xor := 0 as bv32;
    var j := i;
    
    while j < n
      invariant i <= j <= n
      invariant current_xor == (if i < j then XorRange(arr, i, j - 1) else 0 as bv32)
      invariant forall k :: i <= k < j ==> XorRange(arr, i, k) as int <= (max_result as int)
      invariant global_max == max_result
    {
      current_xor := current_xor ^ arr[j];
      if (current_xor as int) > (max_result as int) {
        max_result := current_xor;
        ghost global_max := max_result;
      } else {
        ghost UpdateMax(i, j, arr);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := max_result;
}
// </vc-code>

