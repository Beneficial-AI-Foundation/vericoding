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

// <vc-helpers>
function sumInRangeIter(N: int, A: int, B: int): int
  requires N >= 0
  requires A >= 1 && A <= B && B <= 36
  decreases N
{
  if N == 0 then 0
  else if A <= digitSum(N) <= B then N + sumInRangeIter(N-1, A, B)
  else sumInRangeIter(N-1, A, B)
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
  var result := 0;
  var currentN := N;
  while currentN > 0
    invariant 0 <= currentN <= N
    invariant result == sumInRange(N, A, B) - sumInRange(currentN, A, B)
  {
    if A <= digitSum(currentN) <= B {
      result := result + currentN;
    }
    currentN := currentN - 1;
  }
  return result;
}
// </vc-code>

