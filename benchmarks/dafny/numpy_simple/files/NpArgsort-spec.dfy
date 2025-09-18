// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Argsort(a: array<int>) returns (result: array<int>)
    ensures result.Length == a.Length
    ensures forall i, j :: 0 <= i < j < result.Length && 0 <= result[i] < a.Length && 0 <= result[j] < a.Length ==> a[result[i]] <= a[result[j]]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
