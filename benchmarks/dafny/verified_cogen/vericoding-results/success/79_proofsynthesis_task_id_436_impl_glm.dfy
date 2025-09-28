// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsNegative(x: int) {
  x < 0
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
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall x :: x in negative_list ==> IsNegative(x)
    invariant forall j :: 0 <= j < i && IsNegative(arr[j]) ==> arr[j] in negative_list
  {
    if IsNegative(arr[i]) {
      negative_list := negative_list + [arr[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
