// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ParityMatchAt(arr: array<int>, i: int): bool
  requires 0 <= i < arr.Length
  reads arr
{
  (i % 2) == (arr[i] % 2)
}
// </vc-helpers>

// <vc-spec>
method IsEvenAtEvenIndex(arr: array<int>) returns (result: bool)
    ensures result == forall i :: 0 <= i < arr.Length ==> ((i % 2) == (arr[i] % 2))
// </vc-spec>
// <vc-code>
{
  result := forall i :: 0 <= i < arr.Length ==> ((i % 2) == (arr[i] % 2));
}
// </vc-code>
