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
lemma Power2Positive(k: int)
  requires k >= 0
  ensures power2(k) >= 1
{
  if k > 0 {
    Power2Positive(k - 1);
  }
}

lemma Power2Monotonic(k1: int, k2: int)
  requires 0 <= k1 <= k2
  ensures power2(k1) <= power2(k2)
{
  if k1 < k2 {
    Power2Monotonic(k1, k2 - 1);
    assert power2(k2) == 2 * power2(k2 - 1);
  }
}

function findC(q: int): (c: int)
  requires ValidQuery(q)
  ensures 1 <= c <= 26
  ensures power2(c) - 1 >= q
  ensures c == 1 || power2(c-1) - 1 < q
{
  findCHelper(q, 1)
}

function findCHelper(q: int, c: int): (result: int)
  requires ValidQuery(q)
  requires 1 <= c <= 26
  ensures 1 <= result <= 26
  ensures power2(result) - 1 >= q
  ensures result == 1 || power2(result-1) - 1 < q
  decreases 26 - c
{
  if c > 26 then 26
  else if power2(c) - 1 >= q then c
  else findCHelper(q, c + 1)
}

lemma FindCCorrect(q: int)
  requires ValidQuery(q)
  ensures let c := findC(q) in
    power2(c) - 1 >= q &&
    (c == 1 || power2(c-1) - 1 < q)
{
  var c := findC(q);
  assert power2(c) - 1 >= q;
  if c > 1 {
    var prev := power2(c-1) - 1;
    assert prev < q;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<int>) returns (results: seq<int>)
  requires ValidQueries(queries)
  ensures ValidResults(queries, results)
// </vc-spec>
// <vc-code>
{
  results := [];
  var i := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|
    invariant |results| == i
    invariant ValidResults(queries[0..i], results)
  {
    var query := queries[i];
    var c := findC(query);
    var mersenne := power2(c) - 1;
    var result := mersenne;
    
    if mersenne == query {
      if mersenne == 1 {
        result := 1;
      } else {
        result := largestProperDivisor(mersenne);
      }
    }
    
    results := results + [result];
    i := i + 1;
  }
}
// </vc-code>

