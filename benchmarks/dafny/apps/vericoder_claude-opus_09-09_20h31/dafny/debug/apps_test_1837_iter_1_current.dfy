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
    } else {
        assert forall i :: i in s ==> 0 <= i < |A|;
    }
}

lemma CurrentFixedPointsNonNegative(A: seq<int>)
    requires |A| >= 0
    ensures CurrentFixedPoints(A) >= 0
{
    SetCardinalityBound(A);
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
    var current := 0;
    var i := 0;
    
    // Count current fixed points
    while i < n
        invariant 0 <= i <= n
        invariant current == |set j | 0 <= j < i && A[j] == j|
    {
        if A[i] == i {
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
    
    CurrentFixedPointsNonNegative(A);
}
// </vc-code>

