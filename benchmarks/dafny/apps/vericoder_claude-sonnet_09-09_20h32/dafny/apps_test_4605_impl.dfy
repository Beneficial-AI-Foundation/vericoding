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
lemma digitSumNonnegative(n: int)
  requires n >= 0
  ensures digitSum(n) >= 0
{
  if n == 0 {
  } else {
    digitSumNonnegative(n / 10);
  }
}

lemma sumInRangeNonnegative(N: int, A: int, B: int)
  requires N >= 0
  requires A >= 1 && A <= B
  ensures sumInRange(N, A, B) >= 0
{
  if N == 0 {
  } else {
    digitSumNonnegative(N);
    sumInRangeNonnegative(N-1, A, B);
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
  var i := 1;
  
  while i <= N
    invariant 1 <= i <= N + 1
    invariant result == sumInRange(i-1, A, B)
  {
    digitSumNonnegative(i);
    var ds := digitSum(i);
    
    if A <= ds <= B {
      result := result + i;
    }
    
    i := i + 1;
  }
  
  sumInRangeNonnegative(N, A, B);
}
// </vc-code>

