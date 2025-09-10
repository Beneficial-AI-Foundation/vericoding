predicate ValidInput(N: int, S: int, A: seq<int>)
{
    N >= 1 && S >= 1 && |A| == N && N <= 3000 && S <= 3000 &&
    forall i :: 0 <= i < N ==> A[i] >= 1 && A[i] <= 3000
}

predicate ValidResult(result: int)
{
    result >= 0 && result < 998244353
}

predicate AllElementsGreaterThanS(A: seq<int>, S: int)
{
    forall i :: 0 <= i < |A| ==> A[i] > S
}

function SingleElementCase(N: int, S: int, A: seq<int>): int
    requires N == 1 && |A| == 1
{
    if S == A[0] then 1 else 0
}

// <vc-helpers>
function sumSeq(s: seq<int>): int
  reads s
  decreases s
{
  if |s| == 0 then 0
  else s[0] + sumSeq(s[1..])
}

// Additional helper predicate for array2 initialization to ensure all elements are 0
predicate IsZeroInitialized(arr: array2<int>, rows: int, cols: int)
    reads arr
{
    forall i, j :: 0 <= i < rows && 0 <= j < cols ==> arr[i, j] == 0
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, S: int, A: seq<int>) returns (result: int)
    requires ValidInput(N, S, A)
    ensures ValidResult(result)
    ensures result % 998244353 == result
    ensures (N == 1 && S == A[0]) ==> result == SingleElementCase(N, S, A)
    ensures (N == 1 && S != A[0]) ==> result == SingleElementCase(N, S, A)
    ensures AllElementsGreaterThanS(A, S) ==> result == 0
// </vc-spec>
// <vc-code>
{
    var dp: array2<int>;
    var MOD: int := 998244353;

    if N == 1 {
        if S == A[0] then { return 1; } else { return 0; }
    }

    if AllElementsGreaterThanS(A, S) {
        return 0;
    }

    dp := new array2<int>(N + 1, S + 1);

    // Initialize dp array with zeros
    // This loop is explicitly needed for verification; Dafny doesn't assume new arrays are zero-initialized
    for i := 0 to N {
        for j := 0 to S {
            dp[i, j] := 0;
        }
    }
    // Assert 0 initialization for verification purposes
    ghost var dp_rows := N + 1;
    ghost var dp_cols := S + 1;
    assert IsZeroInitialized(dp, dp_rows, dp_cols);

    // Base case: dp[0][0] = 1 (empty prefix, sum 0, one way)
    dp[0, 0] := 1;

    for i := 1 to N
        invariant 1 <= i <= N + 1
        invariant forall p, q :: 0 <= p < i && 0 <= q <= S ==> dp[p, q] >= 0 && dp[p, q] < MOD
        invariant forall q :: 0 <= q <= S ==> dp[i, q] == 0
    {
        for j := 0 to S
            invariant 0 <= j <= S + 1
            invariant forall x, y :: 0 <= x < i && 0 <= y <= S ==> dp[x, y] >= 0 && dp[x, y] < MOD
            invariant forall y :: 0 <= y < j ==> dp[i, y] >= 0 && dp[i, y] < MOD
            invariant forall y :: j <= y <= S ==> dp[i, y] == 0 // Elements to the right (or at j) are still 0
        {
            // Case 1: Don't include A[i-1] in the current sum
            dp[i, j] := (dp[i, j] + dp[i - 1, j]) % MOD;
            assert dp[i, j] >= 0; // Ensure non-negativity after modulo
            assert dp[i, j] < MOD; // Ensure less than MOD after modulo

            // Case 2: Include A[i-1] in the current sum, if possible
            if j - A[i-1] >= 0 {
                dp[i, j] := (dp[i, j] + dp[i - 1, j - A[i-1]]) % MOD;
                assert dp[i, j] >= 0; // Ensure non-negativity after modulo
                assert dp[i, j] < MOD; // Ensure less than MOD after modulo
            }
        }
    }

    result := 0;
    for j := 0 to S - 1
        invariant 0 <= j <= S
        invariant result >= 0 && result < MOD
    {
        result := (result + dp[N, j]) % MOD;
        assert result >= 0; // Ensure non-negativity after modulo
        assert result < MOD; // Ensure less than MOD after modulo
    }

    return result;
}
// </vc-code>

