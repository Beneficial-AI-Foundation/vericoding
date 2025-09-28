// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 2): added invariant to prove size postcondition */
  even_numbers := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant |even_numbers| <= i
    invariant forall k :: 0 <= k < |even_numbers| ==> even_numbers[k] % 2 == 0
    invariant forall x :: x in even_numbers ==> x in arr[..i]
    invariant forall j :: 0 <= j < i && arr[j] % 2 == 0 ==> arr[j] in even_numbers
  {
    if arr[i] % 2 == 0 {
      even_numbers := even_numbers + [arr[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
