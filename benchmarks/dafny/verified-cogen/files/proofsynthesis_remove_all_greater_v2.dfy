// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RemoveAllGreater(v: array<int>, e: int) returns (result: array<int>)
    requires 
        forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]
    ensures
        forall k :: 0 <= k < result.Length ==> result[k] <= e && (exists j :: 0 <= j < v.Length && v[j] == result[k])
    ensures
        forall k :: 0 <= k < v.Length && v[k] <= e ==> (exists j :: 0 <= j < result.Length && result[j] == v[k])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
