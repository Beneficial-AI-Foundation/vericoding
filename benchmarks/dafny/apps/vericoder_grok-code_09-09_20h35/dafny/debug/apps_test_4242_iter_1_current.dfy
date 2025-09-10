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

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, K: int) returns (result: int)
  requires ValidInput(A, B, K)
  ensures IsKthLargestCommonDivisor(A, B, K, result)
// </vc-spec>
// <vc-code>
{
  var min_val := if A < B then A else B;
  var k_copy := K;
  var d := min_val;
  while d >= 1
    invariant d >= 0
    invariant k_copy >= 0
  {
    if A % d == 0 && B % d == 0 {
      k_copy := k_copy - 1;
      if k_copy == 0 {
        result := d;
        return;
      }
    }
    d := d - 1;
  }
  // Should not reach here due to ValidInput
}
// </vc-code>

