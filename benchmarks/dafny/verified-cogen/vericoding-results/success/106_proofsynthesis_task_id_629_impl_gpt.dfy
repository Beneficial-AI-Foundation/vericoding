// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsEven(x: int) { x % 2 == 0 }
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers(arr: array<int>) returns (even_numbers: seq<int>)
    ensures |even_numbers| <= arr.Length
    ensures forall i :: 0 <= i < |even_numbers| ==> even_numbers[i] % 2 == 0
    ensures forall x :: x in even_numbers ==> x in arr[..]
    ensures forall i :: 0 <= i < arr.Length && arr[i] % 2 == 0 ==> arr[i] in even_numbers
// </vc-spec>
// <vc-code>
{
  var i := 0;
  even_numbers := [];
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant |even_numbers| <= i
    invariant forall j :: 0 <= j < |even_numbers| ==> even_numbers[j] % 2 == 0
    invariant forall x :: x in even_numbers ==> x in arr[..]
    invariant forall k :: 0 <= k < i && arr[k] % 2 == 0 ==> arr[k] in even_numbers
    decreases arr.Length - i
  {
    if arr[i] % 2 == 0 {
      even_numbers := even_numbers + [arr[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
