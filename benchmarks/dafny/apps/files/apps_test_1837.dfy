Given a permutation of integers 0 to n-1, find the maximum number of fixed points
(positions where a[i] = i) after performing at most one swap operation.

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

method solve(n: int, A: seq<int>) returns (result: int)
    requires ValidInput(n, A)
    ensures result == MaxPossibleFixedPoints(A)
    ensures result >= 0
{
    // Count current fixed points
    var cnt := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant cnt == |set j | 0 <= j < i && A[j] == j|
    {
        if A[i] == i {
            // Help Dafny understand the cardinality change
            var oldSet := set j | 0 <= j < i && A[j] == j;
            var newSet := set j | 0 <= j < i+1 && A[j] == j;
            assert newSet == oldSet + {i};
            assert i !in oldSet;
            assert |newSet| == |oldSet| + 1;
            cnt := cnt + 1;
        } else {
            // Help Dafny understand that the set doesn't change in size
            var oldSet := set j | 0 <= j < i && A[j] == j;
            var newSet := set j | 0 <= j < i+1 && A[j] == j;
            assert newSet == oldSet;
            assert |newSet| == |oldSet|;
        }
        i := i + 1;
    }

    // After the loop, cnt equals the total number of fixed points
    assert cnt == |set j | 0 <= j < n && A[j] == j|;
    assert cnt == CurrentFixedPoints(A);

    // If all are already fixed
    if cnt == n {
        result := n;
        return;
    }

    // Check if we can create 2 new fixed points with one swap
    var canCreate2 := false;
    i := 0;
    while i < n && !canCreate2
        invariant 0 <= i <= n
        invariant canCreate2 ==> exists j :: 0 <= j < n && A[j] != j && A[A[j]] == j
        invariant !canCreate2 ==> forall j :: 0 <= j < i ==> A[j] == j || A[A[j]] != j
    {
        if A[i] != i && A[A[i]] == i {
            canCreate2 := true;
        }
        i := i + 1;
    }

    if canCreate2 {
        assert exists i :: 0 <= i < n && A[i] != i && A[A[i]] == i;
        result := cnt + 2;
    } else {
        assert forall i :: 0 <= i < n ==> A[i] == i || A[A[i]] != i;
        result := cnt + 1;
    }
}
