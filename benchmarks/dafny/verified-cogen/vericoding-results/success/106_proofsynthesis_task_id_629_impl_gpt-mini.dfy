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
  var res: seq<int> := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant |res| <= i
    invariant forall k :: 0 <= k < |res| ==> res[k] % 2 == 0
    invariant forall k :: 0 <= k < |res| ==> res[k] in arr[..i]
    invariant forall j :: 0 <= j < i && arr[j] % 2 == 0 ==> arr[j] in res
  {
    if arr[i] % 2 == 0 {
      res := res + [arr[i]];
    }
    i := i + 1;
  }
  even_numbers := res;
}
// </vc-code>
