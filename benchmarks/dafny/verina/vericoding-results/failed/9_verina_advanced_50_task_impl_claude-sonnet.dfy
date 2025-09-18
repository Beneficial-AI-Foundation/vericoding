// <vc-preamble>
predicate IsSorted(v: seq<nat>)
{
    forall i, j :: 0 <= i < j < |v| ==> v[i] <= v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Simplified lemmas to match actual verification needs */
lemma SortedExtension(arr: seq<nat>, x: nat)
    requires IsSorted(arr)
    requires |arr| == 0 || arr[|arr|-1] <= x
    ensures IsSorted(arr + [x])
{
}

lemma MultisetConcat(s1: seq<nat>, s2: seq<nat>)
    ensures multiset(s1 + s2) == multiset(s1) + multiset(s2)
{
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
{
    /* code modified by LLM (iteration 5): Fixed loop entry by ensuring j is initialized properly */
    result := new nat[a1.Length + a2.Length];
    var i, j, k := 0, 0, 0;
    
    while i < a1.Length && j < a2.Length
        invariant 0 <= i <= a1.Length
        invariant 0 <= j <= a2.Length
        invariant k == i + j
        invariant 0 <= k <= result.Length
        invariant IsSorted(result[..k])
        invariant multiset(result[..k]) == multiset(a1[..i]) + multiset(a2[..j])
        invariant i < a1.Length ==> (k == 0 || result[k-1] <= a1[i])
        invariant j < a2.Length ==> (k == 0 || result[k-1] <= a2[j])
        decreases a1.Length - i + a2.Length - j
    {
        if a1[i] <= a2[j] {
            result[k] := a1[i];
            SortedExtension(result[..k], a1[i]);
            i := i + 1;
        } else {
            result[k] := a2[j];
            SortedExtension(result[..k], a2[j]);
            j := j + 1;
        }
        k := k + 1;
    }
    
    while i < a1.Length
        invariant 0 <= i <= a1.Length
        invariant j == a2.Length
        invariant k == i + j
        invariant 0 <= k <= result.Length
        invariant IsSorted(result[..k])
        invariant multiset(result[..k]) == multiset(a1[..i]) + multiset(a2[..])
        invariant i < a1.Length ==> (k == 0 || result[k-1] <= a1[i])
        decreases a1.Length - i
    {
        result[k] := a1[i];
        SortedExtension(result[..k], a1[i]);
        i := i + 1;
        k := k + 1;
    }
    
    while j < a2.Length
        invariant 0 <= j <= a2.Length
        invariant i == a1.Length
        invariant k == i + j
        invariant 0 <= k <= result.Length
        invariant IsSorted(result[..k])
        invariant multiset(result[..k]) == multiset(a1[..]) + multiset(a2[..j])
        invariant j < a2.Length ==> (k == 0 || result[k-1] <= a2[j])
        decreases a2.Length - j
    {
        result[k] := a2[j];
        SortedExtension(result[..k], a2[j]);
        j := j + 1;
        k := k + 1;
    }
    
    assert k == a1.Length + a2.Length == result.Length;
    assert result[..k] == result[..];
}
// </vc-code>
