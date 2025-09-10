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
function CommonDivisorsInDescendingOrder(A: int, B: int): seq<int>
  requires A > 0 && B > 0
  ensures forall i, j :: 0 <= i < j < |CommonDivisorsInDescendingOrder(A, B)| ==> CommonDivisorsInDescendingOrder(A, B)[i] > CommonDivisorsInDescendingOrder(A, B)[j]
  ensures |CommonDivisorsInDescendingOrder(A, B)| == |CommonDivisors(A, B)|
  ensures forall d :: d in CommonDivisors(A, B) <==> d in CommonDivisorsInDescendingOrder(A,B)
{
  var temp_divs: seq<int> := [];
  var d := A;
  while d >= 1
    invariant d >= 0
    invariant forall i, j :: 0 <= i < j < |temp_divs| ==> temp_divs[i] > temp_divs[j]
    invariant forall x :: x in CommonDivisors(A,B) && x > d <==> x in temp_divs
  {
    if A % d == 0 && B % d == 0 {
      temp_divs := temp_divs + [d];
    }
    d := d - 1;
  }
  return temp_divs;
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, K: int) returns (result: int)
  requires ValidInput(A, B, K)
  ensures IsKthLargestCommonDivisor(A, B, K, result)
// </vc-spec>
// <vc-code>
{
    var divisors := CommonDivisorsInDescendingOrder(A, B);
    result := divisors[K - 1];
}
// </vc-code>

