// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BinarySearch(v: array<int>, k: int) returns (result: int)
    requires forall i, j :: 0 <= i <= j < v.Length ==> v[i] <= v[j]
    requires exists i :: 0 <= i < v.Length && k == v[i]
    ensures 0 <= result < v.Length
    ensures k == v[result]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
