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
function Min(a: int, b: int): int
  ensures Min(a, b) == if a < b then a else b
{
  if a < b then aIsh else b
}

function CommonDivisors(A: int, B: int): set<int>
  requires A > 0 && B > 0
{
  set d | 1 <= d <= Min(A, B) && A % d == 0 && B % d == 0
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
    invariant 1 <= d <= min_val + 1
    invariant |set db | 1 <= db < d && A % db == 0 && B % db == 0| == |divisors|
    invariant forall i :: 0 <= i < |divisors| ==> 1 <= divisors[i] < d && A % divisors[i] == 0 && B % divisors[i] == 0
    invariant forall i, j :: 0 <= i < j < |divisors| ==> divisors[i] < divisors[j]
  {
    if A % d == 0 && B % d == 0 {
      divisors := divisors + [d];
    }
    d := d + 1;
  }
  assert |divisors| >= K;
  result := divisors[ |divisors| - K ];
}
// </vc-code>

