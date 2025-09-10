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
function findC(query: int): int
  requires ValidQuery(query)
  ensures 1 <= findC(query) <= 26
  ensures power2(findC(query)) - 1 >= query
  ensures findC(query) == 1 || power2(findC(query) - 1) - 1 < query
{
  var c := 1;
  while c <= 26
    invariant 1 <= c <= 27
    invariant (c == 1 || power2(c - 1) - 1 < query)
  {
    if power2(c) - 1 >= query then
      return c;
    c := c + 1;
  }
  return 26;
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<int>) returns (results: seq<int>)
  requires ValidQueries(queries)
  ensures ValidResults(queries, results)
// </vc-spec>
// <vc-code>
{
  var results_array: array<int> := new int[|queries|];
  var i := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|
    invariant forall k :: 0 <= k < i ==> results_array[k] >= 1
    invariant forall k :: 0 <= k < i ==> 
      var current_query := queries[k];
      var c_val := findC(current_query);
      (c_val == 1 || power2(c_val - 1) - 1 < current_query) &&
      (power2(c_val) - 1 > current_query ==> results_array[k] == power2(c_val) - 1) &&
      (power2(c_val) - 1 == current_query ==> 
        results_array[k] == (if power2(c_val) - 1 <= 1 then 1 else largestProperDivisor(power2(c_val) - 1)))
  {
    var query := queries[i];
    var c := findC(query);

    if power2(c) - 1 > query {
      results_array[i] := power2(c) - 1;
    } else { // power2(c) - 1 == query
      if power2(c) - 1 <= 1 {
        results_array[i] := 1;
      } else {
        results_array[i] := largestProperDivisor(power2(c) - 1);
      }
    }
    i := i + 1;
  }
  return results_array[..];
}
// </vc-code>

