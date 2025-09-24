// <vc-preamble>
predicate ValidInput(N: int, K: int, A: seq<int>)
{
    2 <= K <= N <= 100000 && 
    |A| == N && 
    IsPermutation(A, N)
}

predicate IsPermutation(A: seq<int>, N: int)
{
    |A| == N && 
    (forall i :: 0 <= i < N ==> 1 <= A[i] <= N) &&
    (forall i, j :: 0 <= i < j < N ==> A[i] != A[j])
}

function MinOperations(N: int, K: int): int
    requires 2 <= K <= N
{
    if N == K then 1
    else 1 + (N - 2) / (K - 1)
}

predicate ValidOutput(N: int, K: int, A: seq<int>, result: int)
{
    ValidInput(N, K, A) ==> result == MinOperations(N, K)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SolveMinOperations(N: int, K: int, A: seq<int>) returns (result: int)
    requires ValidInput(N, K, A)
    ensures ValidOutput(N, K, A, result)
// </vc-spec>
// <vc-code>
{
    if N == K {
        result := 1;
    } else {
        result := 1 + (N - 2) / (K - 1);
    }
}
// </vc-code>
