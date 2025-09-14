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
predicate FindAddendsLoopInv(q: seq<int>, x: int, i: int, j: int)
{
    0 <= i < j < |q| && // i and j are valid indices and i < j
    (forall k, l :: (i <= k < l <= j) ==> q[k] + q[l] != x) // No addends in the current window [i..j] smaller than current i and j 
}
// </vc-helpers>

// <vc-spec>
method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
    requires Sorted(q) && HasAddends(q, x)
    ensures i < j < |q| && q[i]+q[j] == x
// </vc-spec>
// <vc-code>
{
    var i_idx := 0;
    var j_idx := |q| - 1;

    while i_idx < j_idx
        invariant 0 <= i_idx < j_idx < |q|
        invariant Sorted(q)
        invariant HasAddends(q, x) ==> (exists k, l :: i_idx <= k < l <= j_idx && q[k] + q[l] == x)
        invariant (forall k, l :: 0 <= k < l < i_idx ==> q[k] + q[l] != x)
        invariant (forall k, l :: j_idx < k < l < |q|  ==> q[k] + q[l] != x)
    {
        var current_sum := q[i_idx] + q[j_idx];
        if current_sum == x {
            return i_idx, j_idx;
        } else if current_sum < x {
            i_idx := i_idx + 1;
        } else {
            j_idx := j_idx - 1;
        }
    }
    // This part should be unreachable if the preconditions hold
    // and a valid pair exists.
    assert false; 
}
// </vc-code>

