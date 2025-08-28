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
lemma AddendsInRangeImpliesAddends(q: seq<int>, x: int, i: nat, j: nat)
    requires AreOreredIndices(q, i, j)
    requires HasAddendsInIndicesRange(q, x, i, j)
    ensures HasAddends(q, x)
{
    var subseq := q[i..(j + 1)];
    assert HasAddends(subseq, x);
    var k, m :| 0 <= k < m < |subseq| && subseq[k] + subseq[m] == x;
    assert q[i + k] + q[i + m] == x;
    assert 0 <= i + k < i + m < |q|;
}

lemma SubsequenceHasAddends(q: seq<int>, x: int, i: nat, j: nat)
    requires Sorted(q)
    requires 0 <= i < j < |q|
    requires HasAddends(q, x)
    ensures HasAddendsInIndicesRange(q, x, i, j) || q[i] + q[j] > x || q[i] + q[j] < x
{
    if exists k, m :: i <= k < m <= j && q[k] + q[m] == x {
        assert HasAddends(q[i..(j + 1)], x);
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
method SearchAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
    requires Sorted(q) && HasAddends(q, x)
    ensures i < j < |q| && q[i] + q[j] == x
{
    i := 0;
    j := |q| - 1;
    while i < j
        decreases j - i
        invariant 0 <= i < j < |q|
        invariant HasAddends(q, x)
        invariant forall k, m :: 0 <= k < m < |q| && q[k] + q[m] == x ==> k >= i && m <= j
    {
        var sum := q[i] + q[j];
        if sum == x {
            return i, j;
        } else if sum < x {
            i := i + 1;
        } else {
            j := j - 1;
        }
    }
    assert false; // This line should be unreachable due to the precondition HasAddends(q, x)
}
// </vc-code>
