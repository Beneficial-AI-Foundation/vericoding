function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}

// <vc-helpers>
// No helpers needed for this verification.
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
// </vc-spec>
// <vc-code>
{
  var n := |numbers|;
  var arr := new int[n];
  arr[0] := numbers[0];
  // base: arr[0] is max of numbers[0..1]
  assert isMax(arr[0], numbers[0..1]);
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant forall j :: 0 <= j < i ==> isMax(arr[j], numbers[0..(j+1)])
  {
    var candidate := numbers[i];
    if candidate > arr[i-1] {
      arr[i] := candidate;
      // prove isMax(arr[i], numbers[0..(i+1)])
      // For k < i: numbers[k] <= arr[i-1] (from isMax(arr[i-1], numbers[0..i])) and arr[i-1] < arr[i], so numbers[k] <= arr[i]
      assert forall k :: 0 <= k < i ==> numbers[k] <= arr[i];
      // For k == i: numbers[i] == candidate == arr[i]
      assert numbers[i] <= arr[i];
      assert isMax(arr[i], numbers[0..(i+1)]);
    } else {
      arr[i] := arr[i-1];
      // prove isMax(arr[i], numbers[0..(i+1)])
      // For k < i: numbers[k] <= arr[i-1] (from isMax(arr[i-1], numbers[0..i])) and arr[i] == arr[i-1], so numbers[k] <= arr[i]
      assert forall k :: 0 <= k < i ==> numbers[k] <= arr[i];
      // For k == i: numbers[i] <= arr[i-1] == arr[i]
      assert numbers[i] <= arr[i];
      assert isMax(arr[i], numbers[0..(i+1)]);
    }
    i := i + 1;
  }
  return arr[..];
}
// </vc-code>

