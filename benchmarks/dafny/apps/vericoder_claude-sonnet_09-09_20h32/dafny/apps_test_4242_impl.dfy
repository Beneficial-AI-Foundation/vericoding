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

lemma GcdDividesBoth(a: int, b: int)
  requires a > 0 && b > 0
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
{
  var g := gcd(a, b);
  if a == b {
    assert g == a;
  } else if a > b {
    GcdDividesBoth(a - b, b);
    assert gcd(a - b, b) == g;
    ModuloLemma(a, b, g);
  } else {
    GcdDividesBoth(a, b - a);
    assert gcd(a, b - a) == g;
    ModuloLemma(b, a, g);
  }
}

lemma ModuloLemma(x: int, y: int, d: int)
  requires x > y > 0 && d > 0
  requires (x - y) % d == 0 && y % d == 0
  ensures x % d == 0
{
  assert x == (x - y) + y;
}

function FilterSmaller(s: seq<int>, pivot: int): seq<int>
{
  if |s| == 0 then []
  else if s[0] < pivot then [s[0]] + FilterSmaller(s[1..], pivot)
  else FilterSmaller(s[1..], pivot)
}

function FilterEqual(s: seq<int>, pivot: int): seq<int>
{
  if |s| == 0 then []
  else if s[0] == pivot then [s[0]] + FilterEqual(s[1..], pivot)
  else FilterEqual(s[1..], pivot)
}

function FilterLarger(s: seq<int>, pivot: int): seq<int>
{
  if |s| == 0 then []
  else if s[0] > pivot then [s[0]] + FilterLarger(s[1..], pivot)
  else FilterLarger(s[1..], pivot)
}

function SortDesc(s: seq<int>): seq<int>
{
  if |s| <= 1 then s
  else 
    var pivot := s[0];
    var smaller := FilterSmaller(s, pivot);
    var equal := FilterEqual(s, pivot);
    var larger := FilterLarger(s, pivot);
    SortDesc(larger) + equal + SortDesc(smaller)
}

lemma SortDescPreservesElements(s: seq<int>)
  ensures forall x :: x in s <==> x in SortDesc(s)
  ensures |s| == |SortDesc(s)|
{
  if |s| <= 1 {
  } else {
    var pivot := s[0];
    var smaller := FilterSmaller(s, pivot);
    var equal := FilterEqual(s, pivot);
    var larger := FilterLarger(s, pivot);
    SortDescPreservesElements(larger);
    SortDescPreservesElements(smaller);
  }
}

lemma CommonDivisorsEquivalence(A: int, B: int, divs: seq<int>)
  requires A > 0 && B > 0
  requires forall j :: 0 <= j < |divs| ==> divs[j] > 0 && A % divs[j] == 0 && B % divs[j] == 0
  requires forall d :: 1 <= d <= A && A % d == 0 && B % d == 0 ==> d in divs
  ensures forall x :: x in CommonDivisors(A, B) <==> x in divs
{
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, K: int) returns (result: int)
  requires ValidInput(A, B, K)
  ensures IsKthLargestCommonDivisor(A, B, K, result)
// </vc-spec>
// <vc-code>
{
  var commonDivs: seq<int> := [];
  var i := 1;
  
  while i <= A
    invariant 1 <= i <= A + 1
    invariant forall j :: 0 <= j < |commonDivs| ==> commonDivs[j] > 0 && A % commonDivs[j] == 0 && B % commonDivs[j] == 0
    invariant forall d :: 1 <= d < i && A % d == 0 && B % d == 0 ==> d in commonDivs
  {
    if A % i == 0 && B % i == 0 {
      commonDivs := commonDivs + [i];
    }
    i := i + 1;
  }
  
  CommonDivisorsEquivalence(A, B, commonDivs);
  var sortedDivs := SortDesc(commonDivs);
  SortDescPreservesElements(commonDivs);
  
  assert |sortedDivs| >= K;
  result := sortedDivs[K - 1];
}
// </vc-code>

