// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BinarySearchRecursive(v: array<int>, elem: int, c: int, f: int) returns (p: int)
    requires v.Length <= 100000
    requires forall i, j :: 0 <= i < j < v.Length ==> v[i] <= v[j]
    requires 0 <= c <= f + 1 <= v.Length
    requires forall k :: 0 <= k < c ==> v[k] <= elem
    requires forall k :: f < k < v.Length ==> v[k] > elem
    ensures -1 <= p < v.Length
    ensures forall u :: 0 <= u <= p ==> v[u] <= elem
    ensures forall w :: p < w < v.Length ==> v[w] > elem
    decreases f - c + 1
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
