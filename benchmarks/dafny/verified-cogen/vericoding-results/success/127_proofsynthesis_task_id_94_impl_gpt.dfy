// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function minInt(a: int, b: int): int { if a < b then a else b }
lemma LtLeTrans(a: int, b: int, c: int)
  ensures a < b && b <= c ==> a <= c
{ }
// </vc-helpers>

// <vc-spec>
method MinSecondValueFirst(arr: array<array<int>>) returns (first_of_min_second: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> arr[i].Length >= 2
    ensures exists i :: (0 <= i < arr.Length && first_of_min_second == arr[i][0] && 
            (forall j :: 0 <= j < arr.Length ==> arr[i][1] <= arr[j][1]))
// </vc-spec>
// <vc-code>
{
  var n := arr.Length;
  var minIdx := 0;
  var i := 1;
  while i < n
    invariant 0 <= minIdx < n
    invariant 1 <= i <= n
    invariant arr[minIdx].Length >= 2
    invariant forall j :: 0 <= j < i ==> arr[j].Length >= 2
    invariant forall j :: 0 <= j < i ==> arr[minIdx][1] <= arr[j][1]
    decreases n - i
  {
    assert arr[i].Length >= 2;
    if arr[i][1] < arr[minIdx][1] {
      minIdx := i;
    }
    i := i + 1;
  }
  first_of_min_second := arr[minIdx][0];
}
// </vc-code>
