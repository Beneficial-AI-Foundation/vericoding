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
predicate IsSwapPair(A: seq<int>, i: int, j: int)
    requires 0 <= i < |A| && 0 <= j < |A|
{
    i != j && A[i] == j && A[j] == i
}

lemma SwapPairExists(A: seq<int>, n: int)
    requires ValidInput(n, A)
    requires exists i :: 0 <= i < n && A[i] != i && A[A[i]] == i
    ensures exists i, j :: 0 <= i < n && 0 <= j < n && IsSwapPair(A, i, j)
{
    var i :| 0 <= i < n && A[i] != i && A[A[i]] == i;
    var j := A[i];
    assert IsSwapPair(A, i, j);
}

lemma NoSwapPairExists(A: seq<int>, n: int)
    requires ValidInput(n, A)
    requires !(exists i, j :: 0 <= i < n && 0 <= j < n && IsSwapPair(A, i, j))
    ensures !(exists i :: 0 <= i < n && A[i] != i && A[A[i]] == i)
{
    if exists i :: 0 <= i < n && A[i] != i && A[A[i]] == i {
        SwapPairExists(A, n);
        assert exists i, j :: 0 <= i < n && 0 <= j < n && IsSwapPair(A, i, j);
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
    var current := CurrentFixedPoints(A);
    var hasSwap := exists i :: 0 <= i < n && A[i] != i && A[A[i]] == i;
    
    if current == n {
        result := n;
    } else if hasSwap {
        SwapPairExists(A, n);
        result := current + 2;
    } else {
        NoSwapPairExists(A, n);
        result := current + 1;
    }
}
// </vc-code>

