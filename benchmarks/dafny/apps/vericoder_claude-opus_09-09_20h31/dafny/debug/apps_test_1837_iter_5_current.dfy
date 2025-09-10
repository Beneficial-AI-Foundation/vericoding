predicate ValidInput(n: int, A: seq<int>)
{
    n >= 1 &&
    |A| == n &&
    (forall i :: 0 <= i < n ==> 0 <= A[i] < n) &&
    (forall i, j :: 0 <= i < j < n ==> A[i] != A[j]) &&
    (forall k {:trigger A[k]} :: 0 <= k < n ==> exists i :: 0 <= i < n && A[i] == k)
}

function CurrentFixedPoints(A: seq<int>): int
    requires |A| >= 0
{
    |set i | 0 <= i < |A| && A[i] == i|
}

function MaxPossibleFixedPoints(A: seq<int>): int
    requires ValidInput(|A|, A)
{
    var current := CurrentFixedPoints(A);
    if current == |A| then 
        |A|
    else if exists i :: 0 <= i < |A| && A[i] != i && A[A[i]] == i then
        current + 2
    else
        current + 1
}

// <vc-helpers>
lemma SetCardinalityBound(A: seq<int>)
    requires |A| >= 0
    ensures |set i | 0 <= i < |A| && A[i] == i| <= |A|
{
    var s := set i | 0 <= i < |A| && A[i] == i;
    if |A| == 0 {
        assert s == {};
        assert |s| == 0;
    } else {
        // First prove that s is a subset of allIndices
        var allIndices := set i {:trigger i in allIndices} | 0 <= i < |A|;
        
        // Prove s is a subset of allIndices
        forall x | x in s
            ensures x in allIndices
        {
            assert x in s;
            assert 0 <= x < |A| && A[x] == x;
            assert 0 <= x < |A|;
            assert x in allIndices;
        }
        assert s <= allIndices;
        
        // The cardinality of allIndices is exactly |A|
        CardinalityOfRange(|A|);
        assert |allIndices| == |A|;
        
        // Since s is a subset of allIndices
        assert |s| <= |allIndices|;
        assert |s| <= |A|;
    }
}

lemma CardinalityOfRange(n: nat)
    ensures |set i {:trigger i >= 0} | 0 <= i < n| == n
{
    if n == 0 {
        assert (set i {:trigger i >= 0} | 0 <= i < 0) == {};
    } else {
        var s := set i {:trigger i >= 0} | 0 <= i < n;
        var s' := set i {:trigger i >= 0} | 0 <= i < n-1;
        assert s == s' + {n-1};
        CardinalityOfRange(n-1);
    }
}

lemma CurrentFixedPointsNonNegative(A: seq<int>)
    requires |A| >= 0
    ensures CurrentFixedPoints(A) >= 0
    ensures CurrentFixedPoints(A) <= |A|
{
    SetCardinalityBound(A);
    assert CurrentFixedPoints(A) == |set i | 0 <= i < |A| && A[i] == i|;
}

lemma SwapImpliesAtLeastTwoNotFixed(A: seq<int>, idx: int)
    requires ValidInput(|A|, A)
    requires 0 <= idx < |A|
    requires A[idx] != idx
    requires A[A[idx]] == idx
    ensures CurrentFixedPoints(A) <= |A| - 2
{
    var current := CurrentFixedPoints(A);
    var fixedSet := set i | 0 <= i < |A| && A[i] == i;
    
    // idx is not a fixed point
    assert idx !in fixedSet;
    
    // A[idx] is also not a fixed point
    var j := A[idx];
    assert 0 <= j < |A|;
    assert A[j] == idx;
    assert j != idx; // because A[idx] != idx
    if A[j] == j {
        assert idx == j; // contradiction
        assert false;
    }
    assert j !in fixedSet;
    
    // So we have at least two elements not in fixedSet
    assert idx != j;
    assert |fixedSet| <= |A| - 2;
    assert current <= |A| - 2;
}

lemma MaxPossibleFixedPointsBound(A: seq<int>)
    requires ValidInput(|A|, A)
    ensures MaxPossibleFixedPoints(A) >= 0
    ensures MaxPossibleFixedPoints(A) <= |A|
{
    CurrentFixedPointsNonNegative(A);
    var current := CurrentFixedPoints(A);
    assert current >= 0 && current <= |A|;
    
    if current == |A| {
        assert MaxPossibleFixedPoints(A) == |A|;
    } else if exists i :: 0 <= i < |A| && A[i] != i && A[A[i]] == i {
        assert MaxPossibleFixedPoints(A) == current + 2;
        assert current < |A|;
        
        // Use the new lemma to prove current <= |A| - 2
        var witness :| 0 <= witness < |A| && A[witness] != witness && A[A[witness]] == witness;
        SwapImpliesAtLeastTwoNotFixed(A, witness);
        assert current <= |A| - 2;
        assert MaxPossibleFixedPoints(A) <= |A|;
    } else {
        assert MaxPossibleFixedPoints(A) == current + 1;
        assert current < |A|;
        assert MaxPossibleFixedPoints(A) <= |A|;
    }
}

lemma LoopInvariantHelper(A: seq<int>, i: int, current: int)
    requires 0 <= i <= |A|
    requires current == |set j | 0 <= j < i && A[j] == j|
    requires i < |A| && A[i] == i
    ensures current + 1 == |set j | 0 <= j < i+1 && A[j] == j|
{
    var s_before := set j | 0 <= j < i && A[j] == j;
    var s_after := set j | 0 <= j < i+1 && A[j] == j;
    
    assert s_after == s_before + {i};
    assert i !in s_before;
    assert |s_after| == |s_before| + 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, A: seq<int>) returns (result: int)
    requires ValidInput(n, A)
    ensures result == MaxPossibleFixedPoints(A)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    CurrentFixedPointsNonNegative(A);
    
    var current := 0;
    var i := 0;
    
    // Count current fixed points
    while i < n
        invariant 0 <= i <= n
        invariant current == |set j | 0 <= j < i && A[j] == j|
        invariant current <= i
    {
        if A[i] == i {
            LoopInvariantHelper(A, i, current);
            current := current + 1;
        }
        i := i + 1;
    }
    
    assert current == CurrentFixedPoints(A);
    
    // If all are fixed points, return n
    if current == n {
        result := n;
        return;
    }
    
    // Check for a beneficial swap
    i := 0;
    var found := false;
    
    while i < n && !found
        invariant 0 <= i <= n
        invariant !found ==> forall k :: 0 <= k < i && A[k] != k ==> A[A[k]] != k
        invariant found ==> exists j :: 0 <= j < n && A[j] != j && A[A[j]] == j
    {
        if A[i] != i && A[A[i]] == i {
            found := true;
        } else {
            i := i + 1;
        }
    }
    
    if found {
        result := current + 2;
    } else {
        result := current + 1;
    }
    
    MaxPossibleFixedPointsBound(A);
}
// </vc-code>

