function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// <vc-helpers>
// Helper predicate to check if one sequence is a rotation of another
predicate IsRotation(a: seq<int>, b: seq<int>)
{
  |a| == |b| && exists k :: 0 <= k < |a| && b == a[k..] + a[..k]
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def move_one_ball(arr: List[int]) -> bool
We have an array 'arr' of N integers arr[1], arr[2], ..., arr[N].The numbers in the array will be randomly ordered. Your task is to determine if it is possible to get an array sorted in non-decreasing order by performing the following operation on the given array: You are allowed to perform right shift operation any number of times.
*/
// </vc-description>

// <vc-spec>
method MoveOneBall(arr: seq<int>) returns (possible: bool)
  ensures possible ==> exists rotated :: |rotated| == |arr| && IsRotation(arr, rotated) && is_sorted(rotated)
  ensures !possible ==> forall rotated :: |rotated| == |arr| && IsRotation(arr, rotated) ==> !is_sorted(rotated)
// </vc-spec>
// <vc-code>
{
  var n := |arr|;
  if n <= 1 {
    return true;
  }
  
  var i := 0;
  var found := false;
  while i < n
    invariant 0 <= i <= n
    invariant found ==> exists k :: 0 <= k < i && is_sorted(arr[k..] + arr[..k])
    invariant !found ==> forall k :: 0 <= k < i ==> !is_sorted(arr[k..] + arr[..k])
  {
    var rotated := arr[i..] + arr[..i];
    if is_sorted(rotated) {
      found := true;
      return true;
    }
    i := i + 1;
  }
  assert !found;
  assert forall k :: 0 <= k < n ==> !is_sorted(arr[k..] + arr[..k]);
  assert forall rotated :: |rotated| == |arr| && IsRotation(arr, rotated) ==> !is_sorted(rotated) by {
    forall rotated | |rotated| == |arr| && IsRotation(arr, rotated) ensures !is_sorted(rotated) {
      var k :| 0 <= k < |arr| && rotated == arr[k..] + arr[..k];
      assert !is_sorted(arr[k..] + arr[..k]);
    }
  }
  return false;
}
// </vc-code>
