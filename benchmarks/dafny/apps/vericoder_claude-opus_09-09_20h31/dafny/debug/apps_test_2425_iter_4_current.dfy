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
lemma Power2Monotonic(k1: int, k2: int)
  requires 0 <= k1 <= k2
  ensures power2(k1) <= power2(k2)
{
  if k1 == k2 {
    // Base case: equal
  } else {
    // k1 < k2
    Power2Monotonic(k1, k2 - 1);
  }
}

lemma Power2Positive(k: int)
  requires k >= 0
  ensures power2(k) >= 1
{
  // By induction on k
}

function findSmallestPowerExponent(a: int, c: int): int
  requires 2 <= a <= power2(25) - 1
  requires 1 <= c <= 26
  requires c == 1 || power2(c - 1) - 1 < a  // Added precondition
  ensures 1 <= findSmallestPowerExponent(a, c) <= 26
  ensures power2(findSmallestPowerExponent(a, c)) - 1 >= a
  ensures findSmallestPowerExponent(a, c) == 1 || power2(findSmallestPowerExponent(a, c) - 1) - 1 < a
  decreases 27 - c
{
  if c == 26 then 26
  else if power2(c) - 1 >= a then c
  else findSmallestPowerExponent(a, c + 1)
}

lemma FindSmallestPowerExponentCorrect(a: int, c: int)
  requires 2 <= a <= power2(25) - 1
  requires 1 <= c <= 26
  requires c == 1 || power2(c - 1) - 1 < a  // Added precondition
  ensures exists k :: 1 <= k <= 26 && k == findSmallestPowerExponent(a, c) &&
    power2(k) - 1 >= a && (k == 1 || power2(k-1) - 1 < a)
{
  var result := findSmallestPowerExponent(a, c);
  assert 1 <= result <= 26;
  assert power2(result) - 1 >= a;
  assert result == 1 || power2(result - 1) - 1 < a;
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
  
  for i := 0 to |queries|
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
    var a := queries[i];
    var c := findSmallestPowerExponent(a, 1);
    FindSmallestPowerExponentCorrect(a, 1);
    
    var mersenneNumber := power2(c) - 1;
    
    var result: int;
    if mersenneNumber > a {
      result := mersenneNumber;
    } else {
      assert mersenneNumber == a;
      if mersenneNumber <= 1 {
        result := 1;
      } else {
        result := largestProperDivisor(mersenneNumber);
      }
    }
    
    results := results + [result];
  }
}
// </vc-code>

