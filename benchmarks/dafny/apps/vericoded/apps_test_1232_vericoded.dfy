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

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
method solve(n_A: int, n_B: int, k: int, m: int, A: seq<int>, B: seq<int>) returns (result: string)
    requires ValidInput(n_A, n_B, k, m, A, B)
    requires IsSorted(A)
    requires IsSorted(B)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> ValidSelection(A, B, k, m)
// </vc-spec>
// <vc-code>
{
    if A[k - 1] < B[|B| - m] {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

