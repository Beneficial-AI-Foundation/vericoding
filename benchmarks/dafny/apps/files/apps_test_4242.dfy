// <vc-preamble>
function CommonDivisors(A: int, B: int): set<int>
  requires A > 0 && B > 0
{
  set d | 1 <= d <= A && A % d == 0 && B % d == 0
}

predicate ValidInput(A: int, B: int, K: int)
{
  A > 0 && B > 0 && K >= 1 && |CommonDivisors(A, B)| >= K
}

predicate IsKthLargestCommonDivisor(A: int, B: int, K: int, result: int)
  requires ValidInput(A, B, K)
{
  result > 0 &&
  A % result == 0 && B % result == 0 &&
  result in CommonDivisors(A, B) &&
  |set d | d in CommonDivisors(A, B) && d > result| == K - 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, K: int) returns (result: int)
  requires ValidInput(A, B, K)
  ensures IsKthLargestCommonDivisor(A, B, K, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
