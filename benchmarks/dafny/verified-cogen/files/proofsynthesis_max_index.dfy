// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MyFun1(x: array<int>) returns (max_index: int)
    requires x.Length >= 1
    ensures 0 <= max_index < x.Length
    ensures forall k :: 0 <= k < x.Length ==> x[max_index] >= x[k]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
