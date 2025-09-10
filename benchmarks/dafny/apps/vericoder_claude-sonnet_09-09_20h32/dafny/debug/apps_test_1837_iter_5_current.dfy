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
lemma CurrentFixedPointsNonNegative(A: seq<int>)
    requires |A| >= 0
    ensures CurrentFixedPoints(A) >= 0
{
}

lemma CurrentFixedPointsBounded(A: seq<int>)
    requires |A| >= 0
    ensures CurrentFixedPoints(A) <= |A|
{
    var fixedPoints := set i | 0 <= i < |A| && A[i] == i;
    var allIndices := set i | 0 <= i < |A|;
    assert fixedPoints <= allIndices;
    assert |fixedPoints| <= |allIndices|;
    assert |allIndices| == |A|;
}

lemma SwapCreatesFixedPoints(A: seq<int>, i: int)
    requires ValidInput(|A|, A)
    requires 0 <= i < |A|
    requires A[i] != i
    requires A[A[i]] == i
    ensures CurrentFixedPoints(A[i := A[i]][A[i] := i]) == CurrentFixedPoints(A) + 2
{
    var j := A[i];
    var newA := A[i := j][j := i];
    
    assert j != i;
    assert 0 <= j < |A|;
    assert newA[i] == i;
    assert newA[j] == j;
    
    var oldFixed := set k | 0 <= k < |A| && A[k] == k;
    var newFixed := set k | 0 <= k < |A| && newA[k] == k;
    
    assert i !in oldFixed;
    assert j !in oldFixed;
    assert i in newFixed;
    assert j in newFixed;
    
    forall k | 0 <= k < |A| && k != i && k != j
        ensures (k in oldFixed) <==> (k in newFixed)
    {
        if k in oldFixed {
            assert A[k] == k;
            assert newA[k] == k;
        }
        if k in newFixed {
            assert newA[k] == k;
            assert A[k] == k;
        }
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
    CurrentFixedPointsBounded(A);
    
    var current := CurrentFixedPoints(A);
    
    if current == n {
        result := n;
        return;
    }
    
    var hasSwap := false;
    for i := 0 to n
        invariant 0 <= i <= n
        invariant hasSwap <==> exists k :: 0 <= k < i && A[k] != k && A[A[k]] == k
    {
        if A[i] != i && A[A[i]] == i {
            hasSwap := true;
            break;
        }
    }
    
    if hasSwap {
        result := current + 2;
    } else {
        result := current + 1;
    }
}
// </vc-code>

