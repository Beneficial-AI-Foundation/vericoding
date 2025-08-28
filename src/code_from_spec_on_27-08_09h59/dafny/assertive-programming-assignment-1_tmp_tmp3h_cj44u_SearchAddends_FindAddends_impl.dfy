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
lemma SubseqHasAddends(q: seq<int>, x: int, start: nat, end: nat, i: nat, j: nat)
    requires start <= i < j <= end < |q|
    requires q[i] + q[j] == x
    ensures HasAddends(q[start..end+1], x)
{
    assert q[start..end+1][i-start] == q[i];
    assert q[start..end+1][j-start] == q[j];
    assert 0 <= i-start < j-start < |q[start..end+1]|;
    assert q[start..end+1][i-start] + q[start..end+1][j-start] == x;
}

lemma SortedSubseq(q: seq<int>, start: nat, end: nat)
    requires Sorted(q) && start <= end < |q|
    ensures Sorted(q[start..end+1])
{
    forall i, j | 0 <= i <= j < |q[start..end+1]|
        ensures q[start..end+1][i] <= q[start..end+1][j]
    {
        assert q[start..end+1][i] == q[start+i];
        assert q[start..end+1][j] == q[start+j];
        assert start <= start+i <= start+j < |q|;
    }
}

lemma HasAddendsPreservationLeft(q: seq<int>, x: int, i: nat, j: nat)
    requires Sorted(q) && 0 <= i < j < |q| && HasAddends(q[i..j+1], x)
    requires q[i] + q[j] < x && i + 1 < j
    ensures HasAddends(q[i+1..j+1], x)
{
    var k, l :| 0 <= k < l < |q[i..j+1]| && q[i..j+1][k] + q[i..j+1][l] == x;
    if k == 0 {
        assert q[i..j+1][k] == q[i];
        assert q[i] + q[j] < x;
        assert l < |q[i..j+1]| - 1;
        assert q[i+1..j+1][k] + q[i+1..j+1][l] == q[i+1] + q[i+1+l] == x;
        assert 0 <= k < l < |q[i+1..j+1]|;
    } else {
        assert 0 < k < l < |q[i..j+1]|;
        assert q[i+1..j+1][k-1] == q[i..j+1][k];
        assert q[i+1..j+1][l-1] == q[i..j+1][l];
        assert 0 <= k-1 < l-1 < |q[i+1..j+1]|;
    }
}

lemma HasAddendsPreservationRight(q: seq<int>, x: int, i: nat, j: nat)
    requires Sorted(q) && 0 <= i < j < |q| && HasAddends(q[i..j+1], x)
    requires q[i] + q[j] > x && i < j - 1
    ensures HasAddends(q[i..j], x)
{
    var k, l :| 0 <= k < l < |q[i..j+1]| && q[i..j+1][k] + q[i..j+1][l] == x;
    if l == |q[i..j+1]| - 1 {
        assert q[i..j+1][l] == q[j];
        assert q[i] + q[j] > x;
        assert l > 0;
        assert q[i..j][k] + q[i..j][l] == q[i+k] + q[i+l] == x;
        assert 0 <= k < l < |q[i..j]|;
    } else {
        assert 0 <= k < l < |q[i..j+1]| - 1;
        assert q[i..j][k] == q[i..j+1][k];
        assert q[i..j][l] == q[i..j+1][l];
        assert 0 <= k < l < |q[i..j]|;
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
    requires Sorted(q) && HasAddends(q, x)
    ensures i < j < |q| && q[i]+q[j] == x
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    i := 0;
    j := |q| - 1;
    
    while i < j
        invariant 0 <= i < j < |q|
        invariant HasAddends(q[i..j+1], x)
        decreases j - i
    {
        var sum := q[i] + q[j];
        if sum == x {
            return i, j;
        } else if sum < x {
            HasAddendsPreservationLeft(q, x, i, j);
            i := i + 1;
        } else {
            HasAddendsPreservationRight(q, x, i, j);
            j := j - 1;
        }
    }
    
    assert false;
}
// </vc-code>
