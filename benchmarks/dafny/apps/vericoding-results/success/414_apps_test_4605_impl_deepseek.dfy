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
lemma digitSumLemma(n: int, d: int, s: int)
  requires n >= 1
  requires d == n % 10
  requires s == digitSum(n / 10)
  ensures digitSum(n) == d + s
{
}

lemma sumInRangeLemma(n: int, A: int, B: int)
  requires n >= 0
  requires A >= 1 && A <= B
  decreases n
  ensures sumInRange(n, A, B) >= 0
{
  if n > 0 {
    sumInRangeLemma(n-1, A, B);
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
  result := 0;
  var i := N;
  while i > 0
    invariant 0 <= i <= N
    invariant result == sumInRange(N, A, B) - sumInRange(i, A, B)
    invariant result >= 0
  {
    var ds := digitSum(i);
    if A <= ds && ds <= B {
      result := result + i;
    }
    i := i - 1;
  }
}
// </vc-code>

