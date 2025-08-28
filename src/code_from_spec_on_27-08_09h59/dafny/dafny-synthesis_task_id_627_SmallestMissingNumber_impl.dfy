// <vc-helpers>
lemma InSeqImpliesBounded(s: seq<int>, k: int, v: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    requires k in s
    requires v == |s|
    ensures k <= v
{
    var idx :| 0 <= idx < |s| && s[idx] == k;
    assert k == s[idx];
    assert s[idx] >= 0;
    assert idx < |s|;
    assert idx < v;
    assert k >= 0;
    if k > v {
        assert k > |s|;
        assert k > idx;
        assert s[idx] < k;
        assert false;
    }
}

lemma SeqLengthProperty(s: seq<int>, v: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    requires v == |s|
    requires forall k :: 0 <= k < v ==> k in s
    ensures v !in s
{
    if v in s {
        var idx :| 0 <= idx < |s| && s[idx] == v;
        assert s[idx] >= 0;
        assert idx < |s| == v;
        assert s[idx] == v;
        assert idx < v;
        assert v == s[idx];
        assert idx < s[idx];
        assert false;
    }
}

lemma NotInSeqWhenGreater(s: seq<int>, v: int, idx: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    requires 0 <= idx < |s|
    requires s[idx] > v
    requires v >= 0
    ensures v !in s
{
    if v in s {
        var vidx :| 0 <= vidx < |s| && s[vidx] == v;
        if vidx <= idx {
            assert s[vidx] <= s[idx];
            assert v <= s[idx];
            assert v < s[idx];
            assert false;
        } else {
            assert s[idx] <= s[vidx];
            assert s[idx] <= v;
            assert s[idx] > v;
            assert false;
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SmallestMissingNumber(s: seq<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures 0 <= v
    ensures v !in s
    ensures forall k :: 0 <= k < v ==> k in s
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    v := 0;
    while v < |s| && s[v] == v
        invariant 0 <= v <= |s|
        invariant forall k :: 0 <= k < v ==> k in s
        invariant forall i :: 0 <= i < v && i < |s| ==> s[i] == i
    {
        assert s[v] == v;
        v := v + 1;
    }
    
    if v < |s| {
        assert s[v] != v;
        assert 0 <= v;
        if v > 0 {
            assert s[v-1] <= s[v];
        }
        assert s[v] >= 0;
        if s[v] < v {
            if v > 0 {
                assert s[v-1] <= s[v];
                assert v-1 <= s[v];
                assert v-1 < v;
                assert s[v] < v;
                assert v-1 < s[v];
                assert false;
            } else {
                assert s[0] >= 0;
                assert s[0] < 0;
                assert false;
            }
        }
        assert s[v] >= v;
        assert s[v] != v;
        assert s[v] > v;
        NotInSeqWhenGreater(s, v, v);
        assert v !in s;
        return;
    }
    
    assert v == |s|;
    assert forall k :: 0 <= k < v ==> k in s;
    SeqLengthProperty(s, v);
    assert v !in s;
}
// </vc-code>
