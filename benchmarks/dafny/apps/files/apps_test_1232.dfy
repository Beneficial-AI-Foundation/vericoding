Given two sorted arrays A and B (non-decreasing order), determine if it's possible 
to select k elements from A and m elements from B such that every selected element 
from A is strictly less than every selected element from B.

predicate ValidInput(n_A: int, n_B: int, k: int, m: int, A: seq<int>, B: seq<int>)
{
    n_A >= 1 && n_B >= 1 &&
    k >= 1 && k <= n_A &&
    m >= 1 && m <= n_B &&
    |A| == n_A &&
    |B| == n_B
}

predicate IsSorted(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
}

predicate ValidSelection(A: seq<int>, B: seq<int>, k: int, m: int)
    requires k >= 1 && k <= |A|
    requires m >= 1 && m <= |B|
{
    A[k - 1] < B[|B| - m]
}

method solve(n_A: int, n_B: int, k: int, m: int, A: seq<int>, B: seq<int>) returns (result: string)
    requires ValidInput(n_A, n_B, k, m, A, B)
    requires IsSorted(A)
    requires IsSorted(B)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> ValidSelection(A, B, k, m)
{
    var largest_from_A := A[k - 1];
    var smallest_from_B := B[|B| - m];

    if largest_from_A < smallest_from_B {
        result := "YES";
    } else {
        result := "NO";
    }
}
