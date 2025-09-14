// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

// <vc-helpers>
lemma Lemma_SortedAppend(s: seq<int>, x: int)
    requires IsSorted(s)
    requires |s| == 0 || x >= s[|s|-1]
    ensures IsSorted(s + [x])
{
    if |s| == 0 {
        calc {
            IsSorted(s + [x]);
        == { assert s + [x] == [x]; }
            IsSorted([x]);
        == { assert forall p,q | 0<=p<q<1 :: false; }
            true;
        }
    } else {
        var s' := s + [x];
        forall p,q | 0<=p<q<|s'||
            ensures s'[p] <= s'[q]
        {
            if q < |s'| {
                if q < |s'| - 1 {
                    assert s'[p] == s[p] && s'[q] == s[q];
                } else if p < |s'| - 1 {
                    assert s'[p] == s[p] && s'[q] == x;
                    assert s[p] <= s[|s| - 1] <= x;
                } else {
                    assert p == |s'| - 1 && q == |s'|;
                }
            }
        }
    }
}

method Insert(s: seq<int>, i: int, x: int) returns (r: seq<int>)
    requires 0 <= i <= |s|
    ensures multiset(r) == multiset(s) + multiset([x])
    ensures |r| == |s| + 1
    ensures forall j | 0 <= j < i :: r[j] == s[j]
    ensures r[i] == x
    ensures forall j | i <= j < |s| :: r[j+1] == s[j]
{
    var left := s[0..i];
    var right := s[i..];
    r := left + [x] + right;
}

lemma Lemma_InsertPreservesSorted(s: seq<int>, i: int, x: int)
    requires 0 <= i <= |s|
    requires IsSorted(s)
    requires (i == 0 || x >= s[i-1])
    requires (i == |s| || x <= s[i])
    ensures IsSorted(Insert(s, i, x))
{
    var newSeq := Insert(s, i, x);
    forall p,q | 0<=p<q<|newSeq|
        ensures newSeq[p] <= newSeq[q]
    {
        if p < i && q < i {
            assert newSeq[p] == s[p];
            assert newSeq[q] == s[q];
            assert s[p] <= s[q];
        } else if p < i && q == i {
            assert newSeq[p] == s[p];
            assert newSeq[q] == x;
            if i>0 {
                assert s[p] <= s[i-1];
                assert s[i-1] <= x;
            }
        } else if p < i && q > i {
            assert newSeq[p] == s[p];
            assert newSeq[q] == s[q-1];
            if i>0 {
                assert s[p] <= s[i-1];
                assert s[i-1] <= x;
            }
            assert x <= s[i];
            assert s[i] <= s[q-1];
        } else if p == i && q > i {
            assert newSeq[p] == x;
            assert newSeq[q] == s[q-1];
            assert x <= s[i];
            assert s[i] <= s[q-1];
        } else if p > i && q > i {
            assert newSeq[p] == s[p-1];
            assert newSeq[q] == s[q-1];
            assert s[p-1] <= s[q-1];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
// </vc-spec>
// <vc-code>
{
    if |s| == 0 {
        return s;
    } else {
        var sorted := InsertionSort(s[0..|s|-1]);
        var last := s[|s|-1];
        var i := 0;
        while i < |sorted| && sorted[i] <= last
            invariant 0 <= i <= |sorted|
            invariant forall j | 0 <= j < i :: sorted[j] <= last
        {
            i := i + 1;
        }
        var newSorted := Insert(sorted, i, last);
        Lemma_InsertPreservesSorted(sorted, i, last);
        return newSorted;
    }
}
// </vc-code>

