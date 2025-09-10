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
function findCFrom(q: int, k: int): int
  requires 1 <= k <= 26
  ensures k <= findCFrom(q, k) <= 26
  ensures power2(findCFrom(q, k)) - 1 >= q
  ensures forall j :: k <= j < findCFrom(q, k) ==> power2(j) - 1 < q
  decreases 26 - k
{
  if power2(k) - 1 >= q then k else findCFrom(q, k + 1)
}

function findC(q: int): int
  ensures 1 <= findC(q) <= 26
  ensures power2(findC(q)) - 1 >= q
  ensures forall j :: 1 <= j < findC(q) ==> power2(j) - 1 < q
{
  findCFrom(q, 1)
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<int>) returns (results: seq<int>)
  requires ValidQueries(queries)
  ensures ValidResults(queries, results)
// </vc-spec>
// <vc-code>
{
  var out: seq<int> := [];
  var i := 0;
  while i < |queries|
    decreases |queries| - i
  {
    var q := queries[i];
    var c := findC(q);
    var p := power2(c) - 1;
    var r := if p > q then p else (if p <= 1 then 1 else largestProperDivisor(p));
    out := out + [r];
    i := i + 1;
  }
  results := out;
}
// </vc-code>

