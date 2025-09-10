predicate ValidInput(n: int, m: int)
{
  n >= m > 0
}

function sum(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}

function count(s: seq<int>, val: int): int
{
  if |s| == 0 then 0 
  else (if s[0] == val then 1 else 0) + count(s[1..], val)
}

predicate OptimalDistribution(result: seq<int>, n: int, m: int)
  requires m > 0
{
  |result| == m &&
  (forall i :: 0 <= i < |result| ==> result[i] > 0) &&
  sum(result) == n &&
  (forall i :: 0 <= i < |result| ==> result[i] == n / m || result[i] == n / m + 1) &&
  count(result, n / m) == m - (n % m) &&
  count(result, n / m + 1) == n % m
}

// <vc-helpers>
lemma DistributionProperties(n: int, m: int)
  requires ValidInput(n, m)
  ensures m - (n % m) >= 0
  ensures n % m >= 0
{
}

lemma CountLemma(s: seq<int>, val1: int, val2: int)
  requires val1 != val2
  ensures count(s, val1) + count(s, val2) <= |s|
{
}

lemma CountUpdate(s: seq<int>, val: int, x: int)
  ensures count(s + [x], val) == count(s, val) + (if x == val then 1 else 0)
{
}

lemma SumUpdate(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: seq<int>)
  requires ValidInput(n, m)
  ensures OptimalDistribution(result, n, m)
// </vc-spec>
// <vc-code>
{
  var base := n / m;
  var remainder := n % m;
  result := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |result| == i
    invariant sum(result) == base * i + (if i <= remainder then i else remainder)
    invariant count(result, base) == (if i <= remainder then 0 else i - remainder)
    invariant count(result, base + 1) == (if i <= remainder then i else remainder)
    decreases m - i
  {
    if i < remainder {
      result := result + [base + 1];
      assert sum(result) == old(sum(result)) + base + 1;
      assert count(result, base + 1) == old(count(result, base + 1)) + 1;
      assert count(result, base) == old(count(result, base));
    } else {
      result := result + [base];
      assert sum(result) == old(sum(result)) + base;
      assert count(result, base) == old(count(result, base)) + 1;
      assert count(result, base + 1) == old(count(result, base + 1));
    }
    i := i + 1;
  }
}
// </vc-code>

