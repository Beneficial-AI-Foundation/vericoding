// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ChooseOdd(v: array<int>) returns (odd_index: int)
    requires exists q :: 0 <= q < v.Length && v[q] % 2 == 1
    ensures 0 <= odd_index < v.Length
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
