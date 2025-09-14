// <vc-preamble>
predicate IsSorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate MultisetEquiv(s1: seq<int>, s2: seq<int>)
{
    multiset(s1) == multiset(s2)
}
method MergeSortedAux(a: seq<int>, b: seq<int>) returns (result: seq<int>)
{
    assume {:axiom} false;
    result := [];
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed multiset slice lemma with proper reasoning */
lemma SortedAppendLemma(s: seq<int>, x: int)
    requires IsSorted(s)
    requires |s| == 0 || s[|s|-1] <= x
    ensures IsSorted(s + [x])
{
}

lemma MultisetSliceLemma(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures multiset(s[..i+1]) == multiset(s[..i]) + multiset([s[i]])
{
    if i == 0 {
        assert s[..1] == [s[0]];
        assert s[..0] == [];
    } else {
        assert s[..i+1] == s[..i] + [s[i]];
    }
}

lemma MultisetConcatLemma(s1: seq<int>, s2: seq<int>, x: int)
    ensures multiset(s1 + s2 + [x]) == multiset(s1 + s2) + multiset([x])
{
}

lemma MultisetExtendLemma(s1: seq<int>, s2: seq<int>, s3: seq<int>, x: int)
    requires multiset(s1) == multiset(s2 + s3)
    ensures multiset(s1 + [x]) == multiset(s2 + s3 + [x])
{
}
// </vc-helpers>

// <vc-spec>
method MergeSorted(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires IsSorted(a)
    requires IsSorted(b)
    ensures IsSorted(result)
    ensures MultisetEquiv(result, a + b)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added multiset extend lemma calls for proper verification */
    var i, j := 0, 0;
    result := [];
    
    while i < |a| || j < |b|
        invariant 0 <= i <= |a|
        invariant 0 <= j <= |b|
        invariant IsSorted(result)
        invariant MultisetEquiv(result, a[..i] + b[..j])
        invariant |result| > 0 && i < |a| ==> result[|result|-1] <= a[i]
        invariant |result| > 0 && j < |b| ==> result[|result|-1] <= b[j]
        decreases |a| - i + |b| - j
    {
        if i >= |a| {
            assert j < |b|;
            MultisetSliceLemma(b, j);
            MultisetExtendLemma(result, a[..i], b[..j], b[j]);
            SortedAppendLemma(result, b[j]);
            result := result + [b[j]];
            j := j + 1;
        } else if j >= |b| {
            assert i < |a|;
            MultisetSliceLemma(a, i);
            MultisetExtendLemma(result, a[..i], b[..j], a[i]);
            SortedAppendLemma(result, a[i]);
            result := result + [a[i]];
            i := i + 1;
        } else if a[i] <= b[j] {
            MultisetSliceLemma(a, i);
            MultisetExtendLemma(result, a[..i], b[..j], a[i]);
            SortedAppendLemma(result, a[i]);
            result := result + [a[i]];
            i := i + 1;
        } else {
            MultisetSliceLemma(b, j);
            MultisetExtendLemma(result, a[..i], b[..j], b[j]);
            SortedAppendLemma(result, b[j]);
            result := result + [b[j]];
            j := j + 1;
        }
    }
    
    assert i == |a| && j == |b|;
    assert a[..i] == a && b[..j] == b;
}
// </vc-code>
