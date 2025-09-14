function f(n: int, x: int): int
  requires x > 0 && n >= x && n % x == 0
{
  var y := n / x;
  y + x * y * (y - 1) / 2
}

predicate IsDivisor(d: int, n: int)
{
  d > 0 && n % d == 0
}

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate NoDuplicates(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// <vc-helpers>
lemma FunctionValueUnique(n: int, d1: int, d2: int)
  requires d1 > 0 && n >= d1 && n % d1 == 0
  requires d2 > 0 && n >= d2 && n % d2 == 0
  requires d1 != d2
  ensures f(n, d1) != f(n, d2)
{
  var y1 := n / d1;
  var y2 := n / d2;
  
  if d1 < d2 {
    assert n / d1 > n / d2;
    assert y1 > y2;
    assert f(n, d1) == y1 + d1 * y1 * (y1 - 1) / 2;
    assert f(n, d2) == y2 + d2 * y2 * (y2 - 1) / 2;
  } else {
    assert d1 > d2;
    assert n / d1 < n / d2;
    assert y1 < y2;
    assert f(n, d1) == y1 + d1 * y1 * (y1 - 1) / 2;
    assert f(n, d2) == y2 + d2 * y2 * (y2 - 1) / 2;
  }
}

lemma FunctionIncreasing(n: int, d1: int, d2: int)
  requires d1 > 0 && n >= d1 && n % d1 == 0
  requires d2 > 0 && n >= d2 && n % d2 == 0
  requires d1 < d2
  ensures f(n, d1) > f(n, d2)
{
  var y1 := n / d1;
  var y2 := n / d2;
  assert n / d1 > n / d2;
  assert y1 > y2;
}

lemma DivisorsSorted(divisors: seq<int>, n: int)
  requires n >= 2
  requires forall d :: d in divisors ==> IsDivisor(d, n)
  requires IsSorted(divisors)
  requires NoDuplicates(divisors)
  requires |divisors| > 0
  ensures forall i, j :: 0 <= i < j < |divisors| ==> f(n, divisors[i]) > f(n, divisors[j])
{
  forall i, j | 0 <= i < j < |divisors|
    ensures f(n, divisors[i]) > f(n, divisors[j])
  {
    assert divisors[i] < divisors[j];
    assert divisors[i] > 0 && n >= divisors[i] && n % divisors[i] == 0;
    assert divisors[j] > 0 && n >= divisors[j] && n % divisors[j] == 0;
    FunctionIncreasing(n, divisors[i], divisors[j]);
  }
}

lemma NoDuplicatesFValues(divisors: seq<int>, n: int)
  requires n >= 2
  requires forall d :: d in divisors ==> IsDivisor(d, n)
  requires NoDuplicates(divisors)
  requires |divisors| > 0
  ensures NoDuplicates(seq(|divisors|, k requires 0 <= k < |divisors| => f(n, divisors[k])))
{
  forall i, j | 0 <= i < j < |divisors|
    ensures f(n, divisors[i]) != f(n, divisors[j])
  {
    assert divisors[i] > 0 && n >= divisors[i] && n % divisors[i] == 0;
    assert divisors[j] > 0 && n >= divisors[j] && n % divisors[j] == 0;
    FunctionValueUnique(n, divisors[i], divisors[j]);
  }
}

lemma DivisorProperties(divisors: seq<int>, n: int)
  requires n >= 2
  requires forall d :: d in divisors <==> IsDivisor(d, n)
  requires IsSorted(divisors)
  requires NoDuplicates(divisors)
  ensures |divisors| > 0
  ensures 1 in divisors
  ensures n in divisors
  ensures forall d :: d in divisors ==> d > 0 && d <= n
{
  assert IsDivisor(1, n);
  assert IsDivisor(n, n);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
  requires n >= 2
  ensures NoDuplicates(result)
  ensures IsSorted(result)
  ensures forall v :: v in result <==> exists d :: IsDivisor(d, n) && v == f(n, d)
  ensures |result| > 0
// </vc-spec>
// <vc-code>
{
  var divisors: seq<int> := [];
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant forall d :: d in divisors <==> (d < i && IsDivisor(d, n))
    invariant IsSorted(divisors)
    invariant NoDuplicates(divisors)
  {
    if n % i == 0 {
      divisors := divisors + [i];
    }
    i := i + 1;
  }
  
  assert forall d :: d in divisors <==> IsDivisor(d, n);
  DivisorProperties(divisors, n);
  
  result := [];
  var j := |divisors| - 1;
  
  while j >= 0
    invariant -1 <= j < |divisors|
    invariant forall v :: v in result <==> exists k :: j < k < |divisors| && v == f(n, divisors[k])
    invariant IsSorted(result)
    invariant NoDuplicates(result)
    decreases j
  {
    assert 0 <= j < |divisors|;
    assert divisors[j] > 0 && n >= divisors[j] && n % divisors[j] == 0;
    var fValue := f(n, divisors[j]);
    result := [fValue] + result;
    
    j := j - 1;
  }
}
// </vc-code>

