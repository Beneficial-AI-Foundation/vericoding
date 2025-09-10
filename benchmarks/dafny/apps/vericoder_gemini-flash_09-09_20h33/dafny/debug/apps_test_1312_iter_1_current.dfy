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
    var q := n / m;
    var r := n % m;
    result := new int[m];

    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant |result| == m
        invariant forall k :: 0 <= k < i ==> result[k] == q || result[k] == q + 1
        invariant forall k :: 0 <= k < i ==> result[k] > 0
        invariant (forall k :: 0 <= k < i && k < r ==> result[k] == q + 1)
        invariant (forall k :: r <= k < i ==> result[k] == q)
        invariant sum(result[0..i]) == i * q + (if i <= r then i else r)
    {
        if i < r {
            result[i] := q + 1;
        } else {
            result[i] := q;
        }
        i := i + 1;
    }

    // Post-loop assertions to help Dafny verify the ensures clause
    assert |result| == m;
    assert forall k :: 0 <= k < |result| ==> result[k] > 0;
    assert sum(result) == n;
    assert (forall i :: 0 <= i < |result| ==> result[i] == n / m || result[i] == n / m + 1);
    assert count(result, n / m) == m - (n % m);
    assert count(result, n / m + 1) == n % m;
}
// </vc-code>

