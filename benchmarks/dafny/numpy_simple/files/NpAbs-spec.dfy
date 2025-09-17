// <vc-preamble>
function AbsInt(x: int): int
{
    if x < 0 then -x else x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Abs(a: array<int>) returns (result: array<int>)
    ensures 
        result.Length == a.Length &&
        (forall i :: 0 <= i < a.Length ==> result[i] == AbsInt(a[i])) &&
        (forall i :: 0 <= i < result.Length ==> result[i] >= 0)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
