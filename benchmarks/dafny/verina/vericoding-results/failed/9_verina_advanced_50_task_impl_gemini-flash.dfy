// <vc-preamble>
predicate IsSorted(v: seq<nat>)
{
    forall i, j :: 0 <= i < j < |v| ==> v[i] <= v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add a helper for the sorted property of the prefix of the result array */
predicate IsPrefixSorted(arr: array<nat>, k: nat)
{
    forall x, y :: 0 <= x < y < k ==> arr[x] <= arr[y]
}
// </vc-helpers>

// <vc-spec>
method MergeSorted(a1: array<nat>, a2: array<nat>) returns (result: array<nat>)
    requires IsSorted(a1[..])
    requires IsSorted(a2[..])
    ensures IsSorted(result[..])
    ensures multiset(result[..]) == multiset(a1[..]) + multiset(a2[..])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): adjusted loop invariants for sortedness and multiset properties to be more precise and facilitate verification. */
{
    var i := 0;
    var j := 0;
    var k := 0;
    result := new nat[a1.Length + a2.Length];

    while i < a1.Length && j < a2.Length
        invariant 0 <= i <= a1.Length
        invariant 0 <= j <= a2.Length
        invariant 0 <= k == i + j <= result.Length
        invariant IsPrefixSorted(result, k)
        invariant multiset(result[0..k]) == multiset(a1[0..i]) + multiset(a2[0..j])
        invariant (i > 0 ==> result[k-1] == a1[i-1])
        invariant (j > 0 ==> result[k-1] == a2[j-1])
        invariant (i > 0 && j==0) ==> IsSorted(a1[0..i])
        invariant (j > 0 && i==0) ==> IsSorted(a2[0..j])
        invariant (i > 0 && j > 0) ==> (result[k-1] == a1[i-1] || result[k-1] == a2[j-1])
    {
        if a1[i] <= a2[j] {
            result[k] := a1[i];
            i := i + 1;
        } else {
            result[k] := a2[j];
            j := j + 1;
        }
        k := k + 1;
    }

    while i < a1.Length
        invariant j == a2.Length
        invariant 0 <= i <= a1.Length
        invariant 0 <= k == i + j <= result.Length
        invariant IsPrefixSorted(result, k)
        invariant multiset(result[0..k]) == multiset(a1[0..i]) + multiset(a2[0..j])
        invariant (i > 0 ==> result[k-1] == a1[i-1])
    {
        result[k] := a1[i];
        i := i + 1;
        k := k + 1;
    }

    while j < a2.Length
        invariant i == a1.Length
        invariant 0 <= j <= a2.Length
        invariant 0 <= k == i + j <= result.Length
        invariant IsPrefixSorted(result, k)
        invariant multiset(result[0..k]) == multiset(a1[0..i]) + multiset(a2[0..j])
        invariant (j > 0 ==> result[k-1] == a2[j-1])
    {
        result[k] := a2[j];
        j := j + 1;
        k := k + 1;
    }
}
// </vc-code>
