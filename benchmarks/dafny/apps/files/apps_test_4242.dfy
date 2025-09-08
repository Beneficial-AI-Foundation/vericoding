Given positive integers A and B, find the K-th largest positive integer that divides both A and B.
The K-th largest common divisor is guaranteed to exist for the given inputs.

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

method MakeDivisors(n: int) returns (divisors: seq<int>)
  requires n > 0
  ensures forall i :: 0 <= i < |divisors| ==> divisors[i] > 0 && n % divisors[i] == 0
  ensures forall d :: d > 0 && n % d == 0 ==> d in divisors
  ensures forall i, j :: 0 <= i < j < |divisors| ==> divisors[i] < divisors[j]
{
  divisors := [];
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant forall k :: 0 <= k < |divisors| ==> divisors[k] > 0 && n % divisors[k] == 0
    invariant forall d :: 1 <= d < i && n % d == 0 ==> d in divisors
    invariant forall k, j :: 0 <= k < j < |divisors| ==> divisors[k] < divisors[j]
    invariant forall k :: 0 <= k < |divisors| ==> divisors[k] < i
  {
    if n % i == 0 {
      divisors := divisors + [i];
    }
    i := i + 1;
  }
}

method solve(A: int, B: int, K: int) returns (result: int)
  requires ValidInput(A, B, K)
  ensures IsKthLargestCommonDivisor(A, B, K, result)
{
  var div_A := MakeDivisors(A);
  var div_B := MakeDivisors(B);

  var common := [];
  var b_set := set j | 0 <= j < |div_B| :: div_B[j];

  for i := 0 to |div_A|
    invariant forall k :: 0 <= k < |common| ==> common[k] > 0 && A % common[k] == 0 && B % common[k] == 0
    invariant forall k, j :: 0 <= k < j < |common| ==> common[k] < common[j]
    invariant forall d :: d in CommonDivisors(A, B) && d in div_A[..i] ==> d in common
    invariant forall k :: 0 <= k < |common| ==> common[k] in div_A[..i]
    invariant forall k :: 0 <= k < |common| ==> common[k] in CommonDivisors(A, B)
  {
    if div_A[i] in b_set {
      common := common + [div_A[i]];
    }
  }

  assert forall d :: d in CommonDivisors(A, B) ==> d in div_A;
  assert forall d :: d in CommonDivisors(A, B) ==> d in b_set;
  assert forall d :: d in CommonDivisors(A, B) ==> d in common;
  assert forall d :: d in common ==> d in CommonDivisors(A, B);
  assert |common| == |CommonDivisors(A, B)|;
  assert |common| >= K;

  result := common[|common| - K];
}
