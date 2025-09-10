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
lemma SortedDivisorsDescending(A: int, B: int) returns (divisors: seq<int>)
  requires A > 0 && B > 0
  ensures |divisors| == |CommonDivisors(A, B)|
  ensures forall i, j :: 0 <= i < j < |divisors| ==> divisors[i] > divisors[j]
  ensures forall d :: d in CommonDivisors(A, B) <==> d in divisors
{
  var allDivisors := set d | 1 <= d <= A && A % d == 0 && B % d == 0;
  divisors := [];
  var d := A;
  while d >= 1
    invariant -1 <= d <= A
    invariant forall x :: x in divisors ==> x in allDivisors
    invariant forall x :: x in allDivisors && x > d ==> x in divisors
    invariant forall i, j :: 0 <= i < j < |divisors| ==> divisors[i] > divisors[j]
  {
    if d in allDivisors {
      divisors := divisors + [d];
    }
    d := d - 1;
  }
}

ghost method GetKthLargestDivisor(A: int, B: int, K: int) returns (result: int)
  requires ValidInput(A, B, K)
  ensures IsKthLargestCommonDivisor(A, B, K, result)
{
  var divisors := SortedDivisorsDescending(A, B);
  result := divisors[K - 1];
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, K: int) returns (result: int)
  requires ValidInput(A, B, K)
  ensures IsKthLargestCommonDivisor(A, B, K, result)
// </vc-spec>
// <vc-code>
{
  result := GetKthLargestDivisor(A, B, K);
}
// </vc-code>

