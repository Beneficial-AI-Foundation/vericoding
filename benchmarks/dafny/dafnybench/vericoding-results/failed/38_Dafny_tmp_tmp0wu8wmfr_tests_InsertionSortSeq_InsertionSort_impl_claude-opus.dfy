// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

// <vc-helpers>
lemma InsertSorted(s: seq<int>, x: int, i: int)
    requires 1 <= i <= |s|
    requires IsSorted(s[..i])
    requires forall j | i <= j < |s| :: s[j] >= x
    ensures i == |s| ==> IsSorted(s[..i][i-1 := x])
    ensures i < |s| ==> IsSorted(s[..i+1][i := s[i-1]][i-1 := x])
{
    if i == |s| {
        var t := s[..i][i-1 := x];
        assert |t| == i;
        forall p, q | 0 <= p < q < |t|
        ensures t[p] <= t[q]
        {
            if p < i - 1 && q < i - 1 {
                assert t[p] == s[p] && t[q] == s[q];
                assert s[p] <= s[q]; // from IsSorted(s[..i])
            } else if p < i - 1 && q == i - 1 {
                assert t[p] == s[p] && t[q] == x;
                assert s[p] <= s[i-1]; // from IsSorted(s[..i])
                // Since we don't have s[i-1] <= x guaranteed, we need a different approach
            }
        }
    } else {
        var t := s[..i+1][i := s[i-1]][i-1 := x];
        assert |t| == i + 1;
        forall p, q | 0 <= p < q < |t|
        ensures t[p] <= t[q]
        {
            if p < i - 1 && q < i - 1 {
                assert t[p] == s[p] && t[q] == s[q];
                assert s[p] <= s[q];
            } else if p < i - 1 && q == i - 1 {
                assert t[p] == s[p] && t[q] == x;
            } else if p < i - 1 && q == i {
                assert t[p] == s[p] && t[q] == s[i-1];
                assert s[p] <= s[i-1];
            } else if p == i - 1 && q == i {
                assert t[p] == x && t[q] == s[i-1];
                assert x <= s[i-1]; // This needs to be ensured by the caller
            }
        }
    }
}

lemma MultisetPreserved(s: seq<int>, i: int, j: int)
    requires 0 <= i < |s| && 0 <= j < |s| && i != j
    ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
    var t := s[i := s[j]][j := s[i]];
    assert t[i] == s[j];
    assert t[j] == s[i];
    assert forall k | 0 <= k < |s| && k != i && k != j :: t[k] == s[k];
}

lemma SortedAfterShift(r: seq<int>, j: int, key: int)
    requires 0 <= j < |r| - 1
    requires IsSorted(r[..j+1])
    requires j + 2 < |r| ==> IsSorted(r[j+2..|r|])
    requires r[j] > key
    requires r[j+1] == key
    requires forall k | j+1 < k < |r| :: r[k] > key
    requires forall p, q | 0 <= p <= j && j+2 <= q < |r| :: r[p] < r[q]
    ensures var r' := r[j+1 := r[j]]; 
            j >= 1 ==> IsSorted(r'[..j]) &&
            j + 3 <= |r'| ==> IsSorted(r'[j+3..|r'|]) &&
            (forall p, q | 0 <= p < j && j+3 <= q < |r'| :: r'[p] < r'[q])
{
}
// </vc-helpers>

// <vc-spec>
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
// </vc-spec>
// <vc-code>
{
    r := s;
    var i := 1;
    
    while i < |r|
        invariant 1 <= i <= |r| + 1
        invariant |r| == |s|
        invariant multiset(r) == multiset(s)
        invariant IsSorted(r[..i])
        invariant i <= |r| ==> forall p, q | 0 <= p < i && i <= q < |r| :: r[p] <= r[q]
    {
        if i >= |r| {
            break;
        }
        var key := r[i];
        var j := i - 1;
        var r_before_inner := r;
        
        while j >= 0 && r[j] > key
            invariant -1 <= j < i
            invariant i < |r|
            invariant |r| == |r_before_inner|
            invariant multiset(r) == multiset(s)
            invariant r[j + 1] == key
            invariant forall k :: j < k < i ==> r[k + 1] > key
            invariant forall k :: i < k < |r| ==> k < |r_before_inner| && r[k] == r_before_inner[k]
            invariant forall k :: 0 <= k <= j ==> r[k] == r_before_inner[k]
            invariant IsSorted(r[..j+1])
            invariant j + 2 <= i ==> IsSorted(r[j+2..i+1])
            invariant forall p, q :: 0 <= p <= j && j + 2 <= q <= i ==> r[p] < r[q]
            invariant forall p, q :: 0 <= p < i && i < q < |r| ==> r[p] <= r[q]
        {
            r := r[j+1 := r[j]];
            j := j - 1;
        }
        
        r := r[j+1 := key];
        assert IsSorted(r[..i+1]);
        i := i + 1;
    }
}
// </vc-code>

