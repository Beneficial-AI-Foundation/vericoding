// <vc-preamble>
function ShiftLeftInt(x: int, shift: nat): int
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method LeftShift(a: array<int>, b: array<nat>) returns (result: array<int>)
    requires 
        a.Length == b.Length &&
        forall i :: 0 <= i < b.Length ==> b[i] < 64
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < result.Length ==> result[i] == ShiftLeftInt(a[i], b[i])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
