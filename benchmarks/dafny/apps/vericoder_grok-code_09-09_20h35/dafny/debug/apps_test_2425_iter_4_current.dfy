function power2(k: int): int
  requires k >= 0
{
  if k == 0 then 1 else 2 * power2(k - 1)
}

predicate ValidQuery(a: int)
{
  2 <= a <= power2(25) - 1
}

predicate ValidQueries(queries: seq<int>)
{
  forall i :: 0 <= i < |queries| ==> ValidQuery(queries[i])
}

function largestProperDivisor(n: int): int
  requires n > 1
  ensures largestProperDivisor(n) >= 1
  ensures largestProperDivisor(n) < n
  ensures n % largestProperDivisor(n) == 0
  ensures forall d :: largestProperDivisor(n) < d < n ==> n % d != 0
{
  largestProperDivisorHelper(n, 2)
}

function largestProperDivisorHelper(n: int, d: int): int
  requires n > 1
  requires d >= 2
  ensures largestProperDivisorHelper(n, d) >= 1
  ensures largestProperDivisorHelper(n, d) < n
  ensures n % largestProperDivisorHelper(n, d) == 0
  ensures forall k :: largestProperDivisorHelper(n, d) < k < n ==> n % k != 0
  decreases n - d
{
  if d * d > n then 1
  else if n % d == 0 then 
    var quotient := n / d;
    if quotient == d then quotient
    else 
      var remainder_check := largestProperDivisorHelper(n, d + 1);
      if quotient > remainder_check then quotient else remainder_check
  else largestProperDivisorHelper(n, d + 1)
}

predicate ValidResults(queries: seq<int>, results: seq<int>)
{
  |results| == |queries| &&
  forall i :: 0 <= i < |results| ==> results[i] >= 1 &&
  forall i :: 0 <= i < |queries| ==> 
    (exists c :: 1 <= c <= 26 && power2(c) - 1 >= queries[i] && 
     (c == 1 || power2(c-1) - 1 < queries[i]) &&
     (power2(c) - 1 > queries[i] ==> results[i] == power2(c) - 1) &&
     (power2(c) - 1 == queries[i] ==> 
       results[i] == (if power2(c) - 1 <= 1 then 1 else largestProperDivisor(power2(c) - 1))))
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(queries: seq<int>) returns (results: seq<int>)
  requires ValidQueries(queries)
  ensures ValidResults(queries, results)
// </vc-spec>
// <vc-code>
{
  var results: seq<int> := [];
  var i := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|
    invariant |results| == i
    invariant forall j :: 0 <= j < i ==> (exists c :: 1 <= c <= 26 && power2(c) - 1 >= queries[j] &&
      (c == 1 || power2(c-1) - 1 < queries[j]) &&
      (power2(c) - 1 > queries[j] ==> results[j] == power2(c) - 1) &&
      (power2(c) - 1 == queries[j] ==> results[j] == (if power2(c) - 1 <= 1 then 1 else largestProperDivisor(power2(c) - 1))))
  {
    var a := queries[i];
    var c := 1;
    while power2(c) - 1 < a
      invariant 1 <= c <= 26
      invariant power2(c-1) - 1 < a
    {
      c := c + 1;
    }
    var next_power_minus_one := power2(c) - 1;
    if next_power_minus_one == a {
      var lpd := 1;
      var d := a / 2;
      while d >= 2
        invariant 1 <= lpd < a
        invariant a % lpd == 0
        invariant forall k :: lpd < k < a ==> !(a % k == 0)
      {
        if a % d == 0 {
          lpd := d;
          break;
        }
        d := d - 1;
      }
      results := results + [lpd];
    } else {
      results := results + [next_power_minus_one];
    }
    i := i + 1;
  }
  return results;
}
// </vc-code>

