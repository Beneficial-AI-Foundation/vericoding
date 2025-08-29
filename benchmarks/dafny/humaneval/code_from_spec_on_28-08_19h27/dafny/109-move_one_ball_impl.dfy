function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// <vc-helpers>
function right_shift(a: seq<int>, k: int): seq<int>
  requires 0 <= k <= |a|
{
  if |a| == 0 then a
  else a[|a|-k..] + a[..|a|-k]
}

lemma right_shift_length(a: seq<int>, k: int)
  requires 0 <= k <= |a|
  ensures |right_shift(a, k)| == |a|
{
}

function is_rotation_sorted(a: seq<int>): bool
{
  |a| == 0 || exists k :: 0 <= k <= |a| && is_sorted(right_shift(a, k))
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def move_one_ball(arr: List[int]) -> bool
We have an array 'arr' of N integers arr[1], arr[2], ..., arr[N].The numbers in the array will be randomly ordered. Your task is to determine if it is possible to get an array sorted in non-decreasing order by performing the following operation on the given array: You are allowed to perform right shift operation any number of times.
*/
// </vc-description>

// <vc-spec>
method move_one_ball(arr: seq<int>) returns (result: bool)
  ensures result <==> is_rotation_sorted(arr)
// </vc-spec>
// <vc-code>
{
  if |arr| == 0 {
    return true;
  }
  
  var k := 0;
  while k <= |arr|
    invariant 0 <= k <= |arr| + 1
    invariant forall i :: 0 <= i < k ==> !is_sorted(right_shift(arr, i))
  {
    var shifted := right_shift(arr, k);
    if is_sorted(shifted) {
      return true;
    }
    k := k + 1;
  }
  
  return false;
}
// </vc-code>
