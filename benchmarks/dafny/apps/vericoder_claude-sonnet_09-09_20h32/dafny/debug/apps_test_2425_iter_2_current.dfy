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
  findCHelper(query, 1)
}

function findCHelper(query: int, c: int): int
  requires ValidQuery(query)
  requires 1 <= c <= 26
  requires c == 1 || power2(c - 1) - 1 < query
  ensures 1 <= findCHelper(query, c) <= 26
  ensures power2(findCHelper(query, c)) - 1 >= query
  ensures findCHelper(query, c) == 1 || power2(findCHelper(query, c) - 1) - 1 < query
  decreases 26 - c
{
  if power2(c) - 1 >= query then c
  else findCHelper(query, c + 1)
}

function computeResult(query: int): int
  requires ValidQuery(query)
  ensures computeResult(query) >= 1
  ensures exists c :: 1 <= c <= 26 && power2(c) - 1 >= query && 
          (c == 1 || power2(c-1) - 1 < query) &&
          (power2(c) - 1 > query ==> computeResult(query) == power2(c) - 1) &&
          (power2(c) - 1 == query ==> 
            computeResult(query) == (if power2(c) - 1 <= 1 then 1 else largestProperDivisor(power2(c) - 1)))
{
  var c := findC(query);
  var mersenne := power2(c) - 1;
  if mersenne > query then mersenne
  else if mersenne <= 1 then 1
  else largestProperDivisor(mersenne)
}

lemma computeResultCorrect(query: int)
  requires ValidQuery(query)
  ensures var result := computeResult(query);
          result >= 1 &&
          exists c :: 1 <= c <= 26 && power2(c) - 1 >= query && 
          (c == 1 || power2(c-1) - 1 < query) &&
          (power2(c) - 1 > query ==> result == power2(c) - 1) &&
          (power2(c) - 1 == query ==> 
            result == (if power2(c) - 1 <= 1 then 1 else largestProperDivisor(power2(c) - 1)))
{
  var c := findC(query);
  assert 1 <= c <= 26;
  assert power2(c) - 1 >= query;
  assert c == 1 || power2(c-1) - 1 < query;
}

lemma largestProperDivisorHelperCorrect(n: int, d: int, quotient: int)
  requires n > 1
  requires d >= 2
  requires n % d == 0
  requires quotient == n / d
  requires quotient == d
  ensures forall k :: quotient < k < n ==> n % k != 0
{
  forall k | quotient < k < n
    ensures n % k != 0
  {
    if n % k == 0 {
      var q := n / k;
      assert n == q * k;
      assert n == quotient * quotient;
      assert q * k == quotient * quotient;
      if q < quotient {
        assert q * k < quotient * k;
        assert quotient * k <= quotient * quotient;
        assert q * k < quotient * quotient;
        assert false;
      } else if q > quotient {
        assert q >= quotient + 1;
        assert q * k >= (quotient + 1) * k;
        assert (quotient + 1) * k > quotient * k;
        assert quotient * k >= quotient * quotient;
        assert q * k > quotient * quotient;
        assert false;
      } else {
        assert q == quotient;
        assert k == quotient;
        assert false;
      }
    }
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
    invariant forall j :: 0 <= j < i ==> results[j] >= 1
    invariant forall j :: 0 <= j < i ==> 
      (exists c :: 1 <= c <= 26 && power2(c) - 1 >= queries[j] && 
       (c == 1 || power2(c-1) - 1 < queries[j]) &&
       (power2(c) - 1 > queries[j] ==> results[j] == power2(c) - 1) &&
       (power2(c) - 1 == queries[j] ==> 
         results[j] == (if power2(c) - 1 <= 1 then 1 else largestProperDivisor(power2(c) - 1))))
  {
    var result := computeResult(queries[i]);
    computeResultCorrect(queries[i]);
    results := results + [result];
    i := i + 1;
  }
}
// </vc-code>

