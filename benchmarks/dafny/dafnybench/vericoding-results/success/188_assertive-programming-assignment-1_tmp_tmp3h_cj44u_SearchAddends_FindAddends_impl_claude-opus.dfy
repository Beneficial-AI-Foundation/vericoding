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
lemma InitialRangeHasAddends(q: seq<int>, x: int)
    requires Sorted(q)
    requires HasAddends(q, x)
    requires |q| >= 2
    ensures HasAddends(q[0..|q|], x)
{
    assert q[0..|q|] == q;
}

lemma TwoPointerInvariant(q: seq<int>, x: int, i: nat, j: nat, sum: int)
    requires Sorted(q)
    requires 0 <= i < j < |q|
    requires sum == q[i] + q[j]
    requires HasAddends(q[i..(j+1)], x)
    requires sum != x
    ensures (sum < x && i + 1 <= j) ==> HasAddends(q[(i+1)..(j+1)], x)
    ensures (sum > x && i <= j - 1) ==> HasAddends(q[i..j], x)
{
    // When sum < x, we need a larger sum, so we move i right
    // The addends must be in the range [i+1..j] because:
    // - If they were at positions (i, k) for some k > i, then q[i] + q[k] would equal x
    // - But we know q[i] + q[j] < x and q is sorted, so q[k] <= q[j]
    // - This would mean q[i] + q[k] <= q[i] + q[j] < x, contradiction
    
    if sum < x && i + 1 <= j {
        var a, b :| 0 <= a < b < |q[i..(j+1)]| && q[i..(j+1)][a] + q[i..(j+1)][b] == x;
        // Convert to original indices
        var a' := i + a;
        var b' := i + b;
        assert q[a'] + q[b'] == x;
        
        if a' == i {
            // If a' == i, then q[i] + q[b'] == x
            // But sum = q[i] + q[j] < x
            // Since q is sorted and b' <= j, we have q[b'] <= q[j]
            // So q[i] + q[b'] <= q[i] + q[j] < x, contradiction
            assert false;
        }
        // Therefore a' > i, so both addends are in [i+1..j]
        assert a' >= i + 1;
        assert b' <= j;
        assert 0 <= a' - (i+1) < b' - (i+1) < |q[(i+1)..(j+1)]|;
        assert q[(i+1)..(j+1)][a' - (i+1)] + q[(i+1)..(j+1)][b' - (i+1)] == x;
    }
    
    // Similar reasoning for sum > x case
    if sum > x && i <= j - 1 {
        var a, b :| 0 <= a < b < |q[i..(j+1)]| && q[i..(j+1)][a] + q[i..(j+1)][b] == x;
        var a' := i + a;
        var b' := i + b;
        assert q[a'] + q[b'] == x;
        
        if b' == j {
            // If b' == j, then q[a'] + q[j] == x
            // But sum = q[i] + q[j] > x
            // Since q is sorted and a' >= i, we have q[a'] >= q[i]
            // So q[a'] + q[j] >= q[i] + q[j] > x, contradiction
            assert false;
        }
        // Therefore b' < j, so both addends are in [i..j-1]
        assert b' <= j - 1;
        assert 0 <= a' - i < b' - i < |q[i..j]|;
        assert q[i..j][a' - i] + q[i..j][b' - i] == x;
    }
}
// </vc-helpers>

// <vc-spec>
method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
    requires Sorted(q) && HasAddends(q, x)
    ensures i < j < |q| && q[i]+q[j] == x
// </vc-spec>
// <vc-code>
{
    var i' := 0;
    var j' := |q| - 1;
    
    // Establish initial invariant
    InitialRangeHasAddends(q, x);
    assert q[0..|q|] == q;
    assert q[i'..(j'+1)] == q;
    
    var sum := q[i'] + q[j'];
    
    while sum != x
        invariant 0 <= i' < j' < |q|
        invariant HasAddends(q[i'..(j'+1)], x)
        invariant sum == q[i'] + q[j']
        decreases j' - i'
    {
        if sum < x {
            TwoPointerInvariant(q, x, i', j', sum);
            i' := i' + 1;
        } else {
            TwoPointerInvariant(q, x, i', j', sum);
            j' := j' - 1;
        }
        sum := q[i'] + q[j'];
    }
    
    i := i';
    j := j';
}
// </vc-code>

