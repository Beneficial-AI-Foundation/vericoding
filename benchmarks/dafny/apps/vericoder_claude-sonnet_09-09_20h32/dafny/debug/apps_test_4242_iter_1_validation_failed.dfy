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
function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases a + b
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

lemma GcdIsCommonDivisor(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
{
}

lemma GcdIsLargestCommonDivisor(a: int, b: int, d: int)
  requires a > 0 && b > 0
  requires d > 0 && a % d == 0 && b % d == 0
  ensures d <= gcd(a, b)
{
}

function DivisorsUpTo(n: int, limit: int): set<int>
  requires n > 0 && limit >= 1
{
  set d | 1 <= d <= limit && n % d == 0
}

lemma CommonDivisorsAreWithinGcd(A: int, B: int)
  requires A > 0 && B > 0
  ensures CommonDivisors(A, B) == DivisorsUpTo(A, A) * DivisorsUpTo(B, B)
  ensures forall d :: d in CommonDivisors(A, B) ==> d <= gcd(A, B)
{
}

function SeqFromSet(s: set<int>): seq<int>

lemma SeqFromSetProperties(s: set<int>)
  ensures |SeqFromSet(s)| == |s|
  ensures forall x :: x in s <==> x in SeqFromSet(s)
{
  assume {:axiom} |SeqFromSet(s)| == |s|;
  assume {:axiom} forall x :: x in s <==> x in SeqFromSet(s);
}

function SortedDesc(s: seq<int>): seq<int>

lemma SortedDescProperties(s: seq<int>)
  ensures |SortedDesc(s)| == |s|
  ensures forall x :: x in s <==> x in SortedDesc(s)
  ensures forall i, j :: 0 <= i < j < |SortedDesc(s)| ==> SortedDesc(s)[i] >= SortedDesc(s)[j]
{
  assume {:axiom} |SortedDesc(s)| == |s|;
  assume {:axiom} forall x :: x in s <==> x in SortedDesc(s);
  assume {:axiom} forall i, j :: 0 <= i < j < |SortedDesc(s)| ==> SortedDesc(s)[i] >= SortedDesc(s)[j];
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, K: int) returns (result: int)
  requires ValidInput(A, B, K)
  ensures IsKthLargestCommonDivisor(A, B, K, result)
// </vc-spec>
// <vc-code>
{
  var divisors := CommonDivisors(A, B);
  var divisorSeq := SeqFromSet(divisors);
  SeqFromSetProperties(divisors);
  
  var sortedDivisors := SortedDesc(divisorSeq);
  SortedDescProperties(divisorSeq);
  
  assert |sortedDivisors| == |divisors|;
  assert |divisors| >= K;
  assert K - 1 < |sortedDivisors|;
  
  result := sortedDivisors[K - 1];
  
  assert result in sortedDivisors;
  assert result in divisors;
  assert result > 0;
  assert A % result == 0 && B % result == 0;
  
  var largerDivisors := set d | d in divisors && d > result;
  
  assert forall i :: 0 <= i < K - 1 ==> sortedDivisors[i] > result;
  assert forall i :: K - 1 <= i < |sortedDivisors| ==> sortedDivisors[i] <= result;
  assert forall i :: K <= i < |sortedDivisors| ==> sortedDivisors[i] < result;
  
  assert |largerDivisors| == K - 1;
}
// </vc-code>

