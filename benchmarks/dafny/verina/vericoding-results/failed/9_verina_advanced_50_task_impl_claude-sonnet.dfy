// <vc-preamble>
predicate IsSorted(v: seq<nat>)
{
    forall i, j :: 0 <= i < j < |v| ==> v[i] <= v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed multiset properties and added explicit slice concatenation lemmas */
lemma AppendSortedLemma(s: seq<nat>, x: nat)
    requires IsSorted(s)
    requires |s| == 0 || s[|s|-1] <= x
    ensures IsSorted(s + [x])
{
    if |s| == 0 {
        assert IsSorted(s + [x]);
    } else {
        var extended := s + [x];
        forall i, j | 0 <= i < j < |extended|
            ensures extended[i] <= extended[j]
        {
            if j < |s| {
                assert extended[i] == s[i] && extended[j] == s[j];
                assert s[i] <= s[j];
            } else {
                assert j == |s|;
                assert extended[j] == x;
                if i < |s| {
                    assert extended[i] == s[i];
                    assert s[i] <= s[|s|-1] <= x;
                }
            }
        }
    }
}

lemma MultisetAppendProperty<T>(s: seq<T>, x: T)
    ensures multiset(s + [x]) == multiset(s) + multiset([x])
{
}

lemma MultisetSliceIncrement<T>(a: seq<T>, i: nat)
    requires i < |a|
    ensures multiset(a[..i+1]) == multiset(a[..i]) + multiset([a[i]])
{
    assert a[..i+1] == a[..i] + [a[i]];
    MultisetAppendProperty(a[..i], a[i]);
}

lemma SliceEquality<T>(arr: array<T>, k: int, val: T)
    requires 0 <= k < arr.Length
    requires arr[k] == val
    ensures arr[..k+1] == arr[..k] + [val]
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
    /* code modified by LLM (iteration 5): Fixed initialization to establish base case invariants */
    result := new nat[a1.Length + a2.Length];
    var i := 0;
    var j := 0;
    var k := 0;
    
    // Establish initial multiset properties
    assert multiset(result[..0]) == multiset([]);
    assert multiset(a1[..0]) == multiset([]);
    assert multiset(a2[..0]) == multiset([]);
    assert multiset(result[..k]) == multiset(a1[..i]) + multiset(a2[..j]);
    
    while i < a1.Length && j < a2.Length
        invariant 0 <= i <= a1.Length
        invariant 0 <= j <= a2.Length
        invariant k == i + j
        invariant k <= result.Length
        invariant IsSorted(result[..k])
        invariant multiset(result[..k]) == multiset(a1[..i]) + multiset(a2[..j])
        invariant i < a1.Length ==> (k == 0 || result[k-1] <= a1[i])
        invariant j < a2.Length ==> (k == 0 || result[k-1] <= a2[j])
    {
        if a1[i] <= a2[j] {
            AppendSortedLemma(result[..k], a1[i]);
            result[k] := a1[i];
            SliceEquality(result, k, a1[i]);
            MultisetSliceIncrement(a1[..], i);
            i := i + 1;
        } else {
            AppendSortedLemma(result[..k], a2[j]);
            result[k] := a2[j];
            SliceEquality(result, k, a2[j]);
            MultisetSliceIncrement(a2[..], j);
            j := j + 1;
        }
        k := k + 1;
    }
    
    // At this point, establish the base case for the second loop
    assert j == a2.Length || i == a1.Length;
    
    while i < a1.Length
        invariant 0 <= i <= a1.Length
        invariant j == a2.Length
        invariant k == i + j
        invariant k <= result.Length
        invariant IsSorted(result[..k])
        invariant multiset(result[..k]) == multiset(a1[..i]) + multiset(a2[..])
        invariant i < a1.Length ==> (k == 0 || result[k-1] <= a1[i])
    {
        AppendSortedLemma(result[..k], a1[i]);
        result[k] := a1[i];
        SliceEquality(result, k, a1[i]);
        MultisetSliceIncrement(a1[..], i);
        i := i + 1;
        k := k + 1;
    }
    
    while j < a2.Length
        invariant i == a1.Length
        invariant 0 <= j <= a2.Length
        invariant k == i + j
        invariant k <= result.Length
        invariant IsSorted(result[..k])
        invariant multiset(result[..k]) == multiset(a1[..]) + multiset(a2[..j])
        invariant j < a2.Length ==> (k == 0 || result[k-1] <= a2[j])
    {
        AppendSortedLemma(result[..k], a2[j]);
        result[k] := a2[j];
        SliceEquality(result, k, a2[j]);
        MultisetSliceIncrement(a2[..], j);
        j := j + 1;
        k := k + 1;
    }
    
    // Final assertion to help postcondition
    assert i == a1.Length && j == a2.Length;
    assert k == a1.Length + a2.Length;
    assert result.Length == a1.Length + a2.Length;
    assert result[..k] == result[..];
}
// </vc-code>
