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
function CommonDivisors(A: int, B: int): set<int>
  requires A > 0 && B > 0
{
  set d | 1 <= d <= min(A, B) && A % d == 0 && B % d == 0
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, K: int) returns (result: int)
  requires ValidInput(A, B, K)
  ensures IsKthLargestCommonDivisor(A, B, K, result)
// </vc-spec>
// <vc-code>
{
  var min_val := if A < B then A else B;
  var divisors: seq<int> := [];
  var d := 1;
  while d <= min_val
    invariant |set db | 1 <= db <= d-1 && A % db == 0 && B % db == 0| == |divisors|
    invariant forall i :: 0 <= i < |divisors| ==> divisors[i] < d
  {
    if A % d == 0 && B % d == 0 {
      divisors := divisors + [d];
    }
    d := d + 1;
  }
  result := divisors[ |divisors| - K ];
}
// </vc-code>

