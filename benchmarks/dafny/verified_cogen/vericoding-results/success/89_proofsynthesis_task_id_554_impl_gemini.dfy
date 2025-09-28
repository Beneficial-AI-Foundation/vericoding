// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindOddNumbers(arr: array<int>) returns (odd_numbers: seq<int>)
    ensures forall x :: x in odd_numbers ==> x % 2 != 0
    ensures forall i :: 0 <= i < arr.Length && arr[i] % 2 != 0 ==> arr[i] in odd_numbers
// </vc-spec>
// <vc-code>
{
  odd_numbers := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall x :: x in odd_numbers ==> x % 2 != 0
    invariant forall j :: 0 <= j < i && arr[j] % 2 != 0 ==> arr[j] in odd_numbers
  {
    if arr[i] % 2 != 0 {
      odd_numbers := odd_numbers + [arr[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
