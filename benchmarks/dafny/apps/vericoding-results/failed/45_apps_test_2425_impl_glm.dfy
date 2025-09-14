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
function findCHelper(a: int, low: int, high: int): int
  requires 2 <= a
  requires 1 <= low <= high <= 26
  requires power2(low) - 1 < a
  requires power2(high) - 1 >= a
  ensures low <= findCHelper(a, low, high) <= high
  ensures power2(findCHelper(a, low, high)) - 1 >= a
  ensures findCHelper(a, low, high) == 1 || power2(findCHelper(a, low, high)-1) - 1 < a
  decreases high - low
{
  if low == high then low
  else
    var mid := (low + high) / 2;
    if power2(mid + 1) - 1 >= a then
      findCHelper(a, low, mid)
    else
      findCHelper(a, mid + 1, high)
}

predicate isPrime(p: int)
  requires p > 1
  ensures isPrime(p) ==> (forall d :: 1 < d < p ==> p % d != 0)
  ensures !isPrime(p) ==> (exists d :: 1 < d < p && p % d == 0)
{
  isPrimeHelper(p, 2)
}

function isPrimeHelper(p: int, d: int): bool
  requires p > 1
  requires d >= 2
  decreases p - d
{
  if d * d > p then true
  else if p % d == 0 then false
  else isPrimeHelper(p, d + 1)
}

function mersennePrimeExponent(c: int): bool
  requires 1 <= c <= 26
  ensures mersennePrimeExponent(c) == (if power2(c) - 1 > 1 then isPrime(power2(c) - 1) else false)
{
  if power2(c) - 1 > 1 then isPrime(power2(c) - 1) else false
}

function findC(a: int): int
  requires 2 <= a <= power2(25)-1
  ensures 1 <= findC(a) <= 26
  ensures power2(findC(a)) - 1 >= a
  ensures findC(a) == 1 || power2(findC(a)-1) - 1 < a
{
  findCHelper(a, 1, 26)
}

function getMersenneResult(c: int): int
  requires 1 <= c <= 26
{
  if power2(c) - 1 <= 1 then 1
  else largestProperDivisor(power2(c) - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<int>) returns (results: seq<int>)
  requires ValidQueries(queries)
  ensures ValidResults(queries, results)
// </vc-spec>
// <vc-code>
{
  var arr := new int[|queries|];
  for i := 0 to |queries|
    invariant 0 <= i <= |queries|
    invariant arr.Length == |queries|
    invariant forall j :: 0 <= j < i ==> 
      let c := findC(queries[j]) in
        power2(c) - 1 >= queries[j] &&
        (c == 1 || power2(c-1) - 1 < queries[j]) &&
        (power2(c) - 1 > queries[j] ==> arr[j] == power2(c) - 1) &&
        (power2(c) - 1 == queries[j] ==> arr[j] == getMersenneResult(c))
  {
    var c := findC(queries[i]);
    if power2(c) - 1 > queries[i] {
      arr[i] := power2(c) - 1;
    } else {
      arr[i] := getMersenneResult(c);
    }
  }
  results := arr[..];
}
// </vc-code>

