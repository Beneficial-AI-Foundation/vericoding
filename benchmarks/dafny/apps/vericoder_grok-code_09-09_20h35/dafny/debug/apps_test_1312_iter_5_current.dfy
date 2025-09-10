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
lemma Lemma_N_Div_Mod(n: int, m: int)
  requires m != 0
  ensures n == (n / m) * m + (n % m)
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
  Lemma_N_Div_Mod(n, m);
  assert n == m * base + remainder;
  result := [];
  var j := 0;
  while j < m - remainder
    invariant |result| == j
    invariant sum(result) == j * base
    invariant (forall k :: 0 <= k < |result| ==> result[k] == base)
  {
    result := result + [base];
    j := j + 1;
  }
  assert |result| == m - remainder;
  var k := 0;
  while k < remainder
    invariant |result| == m - remainder + k
    invariant sum(result) == (m - remainder) * base + k * (base + 1)
    invariant (forall k1 :: 0 <= k1 < m - remainder ==> result[k1] == base)
    invariant (forall k1 :: m - remainder <= k1 < |result| ==> result[k1] == base + 1)
  {
    result := result + [base + 1];
    k := k + 1;
  }
}
// </vc-code>

