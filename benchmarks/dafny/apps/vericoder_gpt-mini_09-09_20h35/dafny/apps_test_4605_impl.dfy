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
// no helpers needed
// </vc-helpers>

// <vc-spec>
method solve(N: int, A: int, B: int) returns (result: int)
  requires ValidInput(N, A, B)
  ensures result == sumInRange(N, A, B)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var i := N;
  result := 0;
  while i > 0
    invariant 0 <= i <= N
    invariant result >= 0
    invariant result == sumInRange(N, A, B) - sumInRange(i, A, B)
    decreases i
  {
    if A <= digitSum(i) <= B {
      assert sumInRange(i, A, B) == i + sumInRange(i-1, A, B);
      result := result + i;
    } else {
      assert sumInRange(i, A, B) == sumInRange(i-1, A, B);
    }
    i := i - 1;
  }
}
// </vc-code>

