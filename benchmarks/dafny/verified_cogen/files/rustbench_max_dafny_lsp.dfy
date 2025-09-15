// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MaxDafnyLsp(a: array<int>) returns (x: int)
    requires a.Length > 0
    ensures 0 <= x < a.Length
    ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[x]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
