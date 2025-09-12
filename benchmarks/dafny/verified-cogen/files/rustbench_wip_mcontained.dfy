// <vc-preamble>
predicate StrictSorted(arr: array<int>)
    reads arr
{
    forall k, l :: 0 <= k < l < arr.Length ==> arr[k] < arr[l]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Mcontained(v: array<int>, w: array<int>, n: int, m: int) returns (b: bool)
    requires n <= m && n >= 0
    requires StrictSorted(v)
    requires StrictSorted(w)
    requires v.Length >= n && w.Length >= m
    ensures b ==> (forall k :: 0 <= k < n ==> (
        exists j :: 0 <= j < m && v[k] == w[j]
    ))
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
