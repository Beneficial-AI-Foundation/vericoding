// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Parity(x: int): int { x % 2 }
predicate SameParity(i: int, x: int) { Parity(i) == Parity(x) }
// </vc-helpers>

// <vc-spec>
method IsOddAtOddIndex(arr: array<int>) returns (result: bool)
    ensures result == forall i :: 0 <= i < arr.Length ==> ((i % 2) == (arr[i] % 2))
// </vc-spec>
// <vc-code>
{
  result := (forall i :: 0 <= i < arr.Length ==> ((i % 2) == (arr[i] % 2)));
}
// </vc-code>
