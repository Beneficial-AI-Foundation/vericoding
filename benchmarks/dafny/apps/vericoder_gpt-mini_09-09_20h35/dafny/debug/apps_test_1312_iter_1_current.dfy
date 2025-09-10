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
// No auxiliary helpers required for this proof.
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: seq<int>)
  requires ValidInput(n, m)
  ensures OptimalDistribution(result, n, m)
// </vc-spec>
// <vc-code>
{
  var q := n / m;
  var r := n % m;
  result := [];
  var i := 0;
  var rcount := 0;
  var ssum := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |result| == i
    invariant ssum == sum(result)
    invariant (forall k :: 0 <= k < |result| ==> result[k] == q || result[k] == q + 1)
    invariant rcount == count(result, q + 1)
    invariant ssum == q * i + rcount
  {
    if i < r {
      result := result + [q + 1];
      rcount := rcount + 1;
      ssum := ssum + q + 1;
    } else {
      result := result + [q];
      ssum := ssum + q;
    }
    i := i + 1;
  }
  // Post-loop checks to satisfy the ensures clause
  assert |result| == m;
  assert (forall k :: 0 <= k < |result| ==> result[k] > 0) by {
    // q >= 1 follows from n >= m > 0, so q and q+1 are > 0
    assert q >= 1;
    // For each element, it's either q or q+1, both > 0
    calc {
      forall k :: 0 <= k < |result| ==> (result[k] == q || result[k] == q + 1);
      ==> forall k :: 0 <= k < |result| ==> result[k] > 0;
    }
  }
  // sum(result) == q*m + rcount and n == q*m + r, so rcount == r and sum == n
  assert ssum == q * m + rcount;
  assert n == q * m + r;
  assert ssum == n;
  assert count(result, q + 1) == r;
  assert count(result, q) == m - r;
}
// </vc-code>

