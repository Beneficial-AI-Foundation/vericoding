// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindNegativeNumbers(arr: array<int>) returns (negative_list: seq<int>)
    ensures forall x :: x in negative_list ==> x < 0
    ensures forall i :: 0 <= i < arr.Length && arr[i] < 0 ==> arr[i] in negative_list
// </vc-spec>
// <vc-code>
{
  var neg: seq<int> := [];
  for i := 0 to arr.Length
    invariant forall x :: x in neg ==> x < 0
    invariant forall j :: 0 <= j < i && arr[j] < 0 ==> arr[j] in neg
  {
    if arr[i] < 0
    {
      neg := neg + [arr[i]];
    }
  }
  negative_list := neg;
}
// </vc-code>
