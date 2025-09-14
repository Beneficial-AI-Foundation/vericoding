// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

// <vc-helpers>
lemma InsertPreservesMultiset(s: seq<int>, x: int, pos: int)
    requires 0 <= pos <= |s|
    ensures multiset(s[..pos] + [x] + s[pos..]) == multiset(s) + multiset{x}
{
    assert s[..pos] + s[pos..] == s;
    assert multiset(s[..pos] + s[pos..]) == multiset(s);
    assert multiset(s[..pos] + [x] + s[pos..]) == multiset(s[..pos]) + multiset([x]) + multiset(s[pos..]);
    assert multiset([x]) == multiset{x};
}

lemma InsertMaintainsSorted(s: seq<int>, x: int, pos: int)
    requires IsSorted(s)
    requires 0 <= pos <= |s|
    requires forall i | 0 <= i < pos :: s[i] <= x
    requires forall i | pos <= i < |s| :: x <= s[i]
    ensures IsSorted(s[..pos] + [x] + s[pos..])
{
    var result := s[..pos] + [x] + s[pos..];
    forall p, q | 0 <= p < q < |result|
        ensures result[p] <= result[q]
    {
        if p < pos && q == pos {
            assert result[p] == s[p];
            assert result[q] == x;
            assert s[p] <= x;
        } else if p == pos && q > pos {
            assert result[p] == x;
            assert result[q] == s[q-1];
            assert x <= s[q-1];
        } else if p < pos && q > pos {
            assert result[p] == s[p];
            assert result[q] == s[q-1];
            assert s[p] <= x <= s[q-1];
        } else if p < pos && q < pos {
            assert result[p] == s[p];
            assert result[q] == s[q];
            assert s[p] <= s[q];
        } else if p > pos && q > pos {
            assert result[p] == s[p-1];
            assert result[q] == s[q-1];
            assert s[p-1] <= s[q-1];
        }
    }
}

method FindInsertPosition(s: seq<int>, x: int) returns (pos: int)
    requires IsSorted(s)
    ensures 0 <= pos <= |s|
    ensures forall i | 0 <= i < pos :: s[i] <= x
    ensures forall i | pos <= i < |s| :: x <= s[i]
{
    pos := 0;
    while pos < |s| && s[pos] <= x
        invariant 0 <= pos <= |s|
        invariant forall i | 0 <= i < pos :: s[i] <= x
    {
        pos := pos + 1;
    }
}

lemma MultisetSubsequence(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures multiset(s[..i]) + multiset{s[i]} == multiset(s[..i+1])
{
    assert s[..i+1] == s[..i] + [s[i]];
    assert multiset(s[..i] + [s[i]]) == multiset(s[..i]) + multiset([s[i]]);
    assert multiset([s[i]]) == multiset{s[i]};
}
// </vc-helpers>

// <vc-spec>
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
// </vc-spec>
// <vc-code>
{
    r := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant multiset(r) == multiset(s[..i])
        invariant IsSorted(r)
    {
        var pos := FindInsertPosition(r, s[i]);
        InsertPreservesMultiset(r, s[i], pos);
        InsertMaintainsSorted(r, s[i], pos);
        var old_r := r;
        r := r[..pos] + [s[i]] + r[pos..];
        
        assert multiset(r) == multiset(old_r) + multiset{s[i]};
        assert multiset(old_r) == multiset(s[..i]);
        MultisetSubsequence(s, i);
        assert multiset(s[..i]) + multiset{s[i]} == multiset(s[..i+1]);
        assert multiset(r) == multiset(s[..i+1]);
        
        i := i + 1;
    }
    assert i == |s|;
    assert s[..|s|] == s;
    assert multiset(r) == multiset(s[..i]) == multiset(s[..|s|]) == multiset(s);
}
// </vc-code>

