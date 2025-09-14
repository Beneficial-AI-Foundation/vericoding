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
lemma lemma_sumInRange_nonneg(n: int, A: int, B: int)
  requires n >= 0
  requires A >= 1 && A <= B
  ensures sumInRange(n, A, B) >= 0
  decreases n
{
  if n == 0 {
    assert sumInRange(n, A, B) == 0;
  } else {
    lemma_sumInRange_nonneg(n - 1, A, B);
    assert n > 0;
    if A <= digitSum(n) <= B {
      assert sumInRange(n, A, B) == n + sumInRange(n - 1, A, B);
      assert sumInRange(n, A, B) >= 0;
    } else {
      assert sumInRange(n, A, B) == sumInRange(n - 1, A, B);
      assert sumInRange(n, A, B) >= 0;
    }
  }
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
  lemma_sumInRange_nonneg(N, A, B);
  return sumInRange(N, A, B);
}
// </vc-code>

