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
        assert forall i :: i in s ==> 0 <= i < |A|;
        var indices := set i | 0 <= i < |A|;
        assert s <= indices;
        assert |s| <= |indices|;
        assert |indices| <= |A|;
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
        assert MaxPossibleFixedPoints(A) <= |A| + 1;
    } else {
        assert MaxPossibleFixedPoints(A) == current + 1;
        assert current < |A|;
        assert MaxPossibleFixedPoints(A) <= |A|;
    }
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
            current := current + 1;
        }
        i := i + 1;
    }
    
    assert current == |set j | 0 <= j < n && A[j] == j|;
    assert current == CurrentFixedPoints(A);
    
    // If all are fixed points, return n
    if current == n {
        result := n;
        assert result == MaxPossibleFixedPoints(A);
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
        assert exists j :: 0 <= j < n && A[j] != j && A[A[j]] == j;
        result := current + 2;
    } else {
        assert forall j :: 0 <= j < n && A[j] != j ==> A[A[j]] != j;
        result := current + 1;
    }
    
    assert result == MaxPossibleFixedPoints(A);
    MaxPossibleFixedPointsBound(A);
}
// </vc-code>

