// <vc-preamble>
predicate ValidInput(N: int, A: int, B: int)
{
  N >= 1 && A >= 1 && A <= B && B <= 36
}

function digitSum(n: int): int
  requires n >= 0
{
  if n == 0 then 0
  else (n % 10) + digitSum(n / 10)
}

function sumInRange(N: int, A: int, B: int): int
  requires N >= 0
  requires A >= 1 && A <= B
{
  if N == 0 then 0
  else if A <= digitSum(N) <= B then N + sumInRange(N-1, A, B)
  else sumInRange(N-1, A, B)
}
// </vc-preamble>

// <vc-helpers>
function ComputeResult(N: int, A: int, B: int): int
  requires N >= 0
  requires A >= 1 && A <= B
{
  if N == 0 then 0
  else if A <= digitSum(N) <= B then N + ComputeResult(N-1, A, B)
  else ComputeResult(N-1, A, B)
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, A: int, B: int) returns (result: int)
  requires ValidInput(N, A, B)
  ensures result == sumInRange(N, A, B)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var currentSum := 0;
  var i := 1;
  while i <= N
    invariant 0 <= i <= N + 1
    invariant currentSum == sumInRange(i-1, A, B)
  {
    if A <= digitSum(i) <= B {
      currentSum := currentSum + i;
    }
    i := i + 1;
  }
  result := currentSum;
}
// </vc-code>
