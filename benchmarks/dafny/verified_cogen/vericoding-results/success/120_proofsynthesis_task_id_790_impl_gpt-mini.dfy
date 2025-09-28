// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IndexParityMatch(i: int, x: int) { i % 2 == x % 2 }
// </vc-helpers>

// <vc-spec>
method IsEvenAtEvenIndex(arr: array<int>) returns (result: bool)
    ensures result == forall i :: 0 <= i < arr.Length ==> ((i % 2) == (arr[i] % 2))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var ok := true;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant ok == (forall j :: 0 <= j < i ==> (j % 2) == (arr[j] % 2))
  {
    ok := ok && ((i % 2) == (arr[i] % 2));
    i := i + 1;
  }
  result := ok;
}
// </vc-code>
