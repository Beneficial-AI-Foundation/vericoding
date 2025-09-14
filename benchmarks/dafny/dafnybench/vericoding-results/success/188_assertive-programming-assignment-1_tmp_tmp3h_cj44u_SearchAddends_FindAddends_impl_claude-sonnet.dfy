predicate Sorted(q: seq<int>)
{
    forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
    exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

predicate IsValidIndex<T>(q: seq<T>, i: nat)
{
    0 <= i < |q|
}

predicate AreOreredIndices<T>(q: seq<T>, i: nat, j: nat)
{
    0 <= i < j < |q|
}

predicate AreAddendsIndices(q: seq<int>, x: int, i: nat, j: nat)
    requires IsValidIndex(q, i) && IsValidIndex(q, j)
{
    q[i] + q[j] == x
}

predicate HasAddendsInIndicesRange(q: seq<int>, x: int, i: nat, j: nat)
    requires AreOreredIndices(q, i, j)
{
    HasAddends(q[i..(j + 1)], x)
}

predicate LoopInv(q: seq<int>, x: int, i: nat, j: nat, sum: int)
{
    AreOreredIndices(q, i, j) &&
    HasAddendsInIndicesRange(q, x, i, j) &&
    AreAddendsIndices(q, sum, i, j)
}

// <vc-helpers>
lemma SortedSliceProperty(q: seq<int>, i: nat, j: nat, k: nat, l: nat)
    requires Sorted(q)
    requires 0 <= i <= k <= l <= j < |q|
    ensures q[i] <= q[k] <= q[l] <= q[j]
{
}

lemma HasAddendsPreservation(q: seq<int>, x: int, left: nat, right: nat)
    requires Sorted(q)
    requires 0 <= left < right < |q|
    requires HasAddends(q[left..(right + 1)], x)
    requires left + 1 < right
    requires q[left] + q[right] < x
    ensures HasAddends(q[(left + 1)..(right + 1)], x)
{
    assert exists i, j {:trigger q[left..(right + 1)][i], q[left..(right + 1)][j]} :: 0 <= i < j < |q[left..(right + 1)]| && q[left..(right + 1)][i] + q[left..(right + 1)][j] == x;
    var i, j :| 0 <= i < j < |q[left..(right + 1)]| && q[left..(right + 1)][i] + q[left..(right + 1)][j] == x;
    
    if i == 0 {
        assert q[left..(right + 1)][i] == q[left];
        assert q[left..(right + 1)][j] == q[left + j];
        assert q[left] + q[left + j] == x;
        assert q[left] + q[right] < x;
        assert j < right - left;
        assert left + j < right;
        SortedSliceProperty(q, left, right, left + j, right);
        assert q[left + j] <= q[right];
        assert q[left] + q[left + j] <= q[left] + q[right] < x;
        assert false;
    }
    
    assert i > 0;
    assert q[(left + 1)..(right + 1)][i - 1] + q[(left + 1)..(right + 1)][j - 1] == x;
    assert 0 <= i - 1 < j - 1 < |q[(left + 1)..(right + 1)]|;
}

lemma HasAddendsPreservationRight(q: seq<int>, x: int, left: nat, right: nat)
    requires Sorted(q)
    requires 0 <= left < right < |q|
    requires HasAddends(q[left..(right + 1)], x)
    requires left < right - 1
    requires q[left] + q[right] > x
    ensures HasAddends(q[left..right], x)
{
    assert exists i, j {:trigger q[left..(right + 1)][i], q[left..(right + 1)][j]} :: 0 <= i < j < |q[left..(right + 1)]| && q[left..(right + 1)][i] + q[left..(right + 1)][j] == x;
    var i, j :| 0 <= i < j < |q[left..(right + 1)]| && q[left..(right + 1)][i] + q[left..(right + 1)][j] == x;
    
    if j == right - left {
        assert q[left..(right + 1)][j] == q[right];
        assert q[left..(right + 1)][i] == q[left + i];
        assert q[left + i] + q[right] == x;
        assert q[left] + q[right] > x;
        assert i > 0;
        assert left + i > left;
        SortedSliceProperty(q, left, right, left, left + i);
        assert q[left] <= q[left + i];
        assert q[left] + q[right] <= q[left + i] + q[right] == x;
        assert false;
    }
    
    assert j < right - left;
    assert q[left..right][i] + q[left..right][j] == x;
    assert 0 <= i < j < |q[left..right]|;
}
// </vc-helpers>

// <vc-spec>
method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
    requires Sorted(q) && HasAddends(q, x)
    ensures i < j < |q| && q[i]+q[j] == x
// </vc-spec>
// <vc-code>
{
    var left: nat := 0;
    var right: nat := |q| - 1;
    
    while left < right
        invariant 0 <= left < right < |q|
        invariant HasAddends(q[left..(right + 1)], x)
    {
        var sum := q[left] + q[right];
        if sum == x {
            return left, right;
        } else if sum < x {
            HasAddendsPreservation(q, x, left, right);
            left := left + 1;
        } else {
            HasAddendsPreservationRight(q, x, left, right);
            right := right - 1;
        }
    }
    
    assert false;
}
// </vc-code>

