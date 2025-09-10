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
  for i := 0 to m - remainder - 1
    invariant |result| == i && forall k :: 0 <= k < |result| ==> result[k] == base && sum(result) == i * base
  {
    result := result + [base];
  }
  for i := remainder to m - 1
    invariant remainder + (i - remainder) == |result| &&
            (forall k :: 0 <= k < m - remainder ==> result[k] == base) &&
            (forall k :: m - remainder <= k < |result| ==> result[k] == base + 1) &&
            sum(result) == (m - remainder) * base + (i - remainder) * (base + 1)
  {
    result := result + [base + 1];
  }
}
// </vc-code>

