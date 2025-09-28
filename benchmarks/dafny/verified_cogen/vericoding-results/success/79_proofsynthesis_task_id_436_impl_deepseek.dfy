// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsNegative(x: int): bool { x < 0 }

function Contains(arr: array<int>, x: int): bool
  reads arr
  ensures Contains(arr, x) == exists i :: 0 <= i < arr.Length && arr[i] == x
{
  exists i | 0 <= i < arr.Length :: arr[i] == x
}
// </vc-helpers>

// <vc-spec>
method FindNegativeNumbers(arr: array<int>) returns (negative_list: seq<int>)
    ensures forall x :: x in negative_list ==> x < 0
    ensures forall i :: 0 <= i < arr.Length && arr[i] < 0 ==> arr[i] in negative_list
// </vc-spec>
// <vc-code>
{
  negative_list := [];
  var index := 0;

  while index < arr.Length
    invariant 0 <= index <= arr.Length
    invariant forall x :: x in negative_list ==> x < 0
    invariant forall i :: 0 <= i < index && arr[i] < 0 ==> arr[i] in negative_list
  {
    if arr[index] < 0 {
      negative_list := negative_list + [arr[index]];
    }
    index := index + 1;
  }
}
// </vc-code>
