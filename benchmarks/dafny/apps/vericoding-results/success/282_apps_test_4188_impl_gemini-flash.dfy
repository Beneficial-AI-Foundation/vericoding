// <vc-preamble>
predicate ValidInput(n: int)
{
    1 <= n <= 16
}

function FactTruthValues(): seq<int>
{
    [1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0]
}

predicate ValidOutput(result: int)
{
    result == 0 || result == 1
}

function ExpectedOutput(n: int): int
    requires ValidInput(n)
{
    FactTruthValues()[n - 1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed compilation error in `IsPrime` predicate by removing the `i * i <= k` condition from the `forall` quantifier as it causes issues when `k` is not known within a bounded set. The predicate `IsPrime` is not used in the `solve` method or `ExpectedOutput` function, so it's not strictly necessary for the current task, but it prevents unnecessary verification errors. */
predicate IsPrime(k: int)
{
  if k < 2 then false
  else if k == 2 then true
  else if k % 2 == 0 then false
  else
    forall i | 3 <= i <= k/2 && i % 2 != 0 :: k % i != 0
}

function ComputeResult(n: int): int
    requires 1 <= n <= 16
{
    FactTruthValues()[n-1]
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures ValidOutput(result)
    ensures result == ExpectedOutput(n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): No changes needed. The previous implementation was correct. */
{
  result := ComputeResult(n);
}
// </vc-code>
