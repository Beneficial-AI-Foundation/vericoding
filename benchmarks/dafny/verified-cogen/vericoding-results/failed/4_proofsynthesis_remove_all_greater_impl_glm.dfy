// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function countLe(a: array<int>, e: int, lo: int, hi: int): int
    requires 0 <= lo <= hi <= a.Length
    reads a
    decreases hi - lo
{
    if lo == hi then 0 else (if a[lo] <= e then 1 else 0) + countLe(a, e, lo+1, hi)
}
/* helper modified by LLM (iteration 5): Fixed helper function to count elements <= e in array slice */
// </vc-helpers>

// <vc-spec>
method RemoveAllGreater(v: array<int>, e: int) returns (result: array<int>)

    requires 
        forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]

    ensures
        forall k :: 0 <= k < result.Length ==> result[k] <= e && result[k] in v[..]
    ensures
        forall k :: 0 <= k < v.Length && v[k] <= e ==> v[k] in result[..]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariants and postcondition proof */
    var n := 0;
    for i := 0 to v.Length
        invariant 0 <= i <= v.Length
        invariant n == countLe(v, e, 0, i)
    {
        if i < v.Length && v[i] <= e {
            n := n + 1;
        }
    }
    result := new int[n];
    var j := 0;
    for i := 0 to v.Length
        invariant 0 <= i <= v.Length
        invariant 0 <= j <= n
        invariant j == countLe(v, e, 0, i)
        invariant forall k :: 0 <= k < j ==> result[k] in v[0..i] && result[k] <= e
        invariant forall k :: 0 <= k < v.Length && v[k] <= e && v[k] in v[0..i] ==> v[k] in result[0..j]
    {
        if i < v.Length && v[i] <= e {
            result[j] := v[i];
            j := j + 1;
        }
    }
}
// </vc-code>
