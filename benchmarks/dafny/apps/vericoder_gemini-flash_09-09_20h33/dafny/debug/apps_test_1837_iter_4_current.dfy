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
predicate CanFormFixedPointPair(A: seq<int>)
    requires |A| >= 0
{
    exists i, j :: 0 <= i < |A| && 0 <= j < |A| && i != j && A[i] == j && A[j] == i
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
    var current_fixed_points := 0;
    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant current_fixed_points == (CountFixedPoints(A, i))
    {
        if A[i] == i {
            current_fixed_points := current_fixed_points + 1;
        }
    }

    if current_fixed_points == n {
        return n;
    } else {
        if exists i :: 0 <= i < n && A[i] != i && A[A[i]] == i {
            return current_fixed_points + 2;
        } else {
            return current_fixed_points + 1;
        }
    }
}
// </vc-code>

