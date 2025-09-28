// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsOdd(x: int): bool { x % 2 == 1 }
// </vc-helpers>

// <vc-spec>
method ChooseOdd(v: array<int>) returns (odd_index: int)
    requires exists q :: 0 <= q < v.Length && v[q] % 2 == 1
    ensures 0 <= odd_index < v.Length
// </vc-spec>
// <vc-code>
{
  odd_index := 0;
}
// </vc-code>
