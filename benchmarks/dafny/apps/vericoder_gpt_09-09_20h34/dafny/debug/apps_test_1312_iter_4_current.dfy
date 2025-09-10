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
lemma SumAppendOne(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
  decreases |s|
{
  if |s| == 0 {
  } else {
    SumAppendOne(s[1..], x);
    assert sum(s + [x]) == (s + [x])[0] + sum((s + [x])[1..]);
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    assert sum(s) == s[0] + sum(s[1..]);
  }
}

lemma CountAppendOne(s: seq<int>, val: int, x: int)
  ensures count(s + [x], val) == count(s, val) + (if x == val then 1 else 0)
  decreases |s|
{
  if |s| == 0 {
  } else {
    CountAppend
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: seq<int>)
  requires ValidInput(n, m)
  ensures OptimalDistribution(result, n, m)
// </vc-spec>
// <vc-code>
lemma SumAppendOne(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
  decreases |s|
{
  if |s| == 0 {
  } else {
    SumAppendOne(s[1..], x);
    assert sum(s + [x]) == (s + [x])[0] + sum((s + [x])[1..]);
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    assert sum(s) == s[0] + sum(s[1..]);
  }
}

lemma CountAppendOne(s: seq<int>, val: int, x: int)
  ensures count(s + [x], val) == count(s, val) + (if x == val then 1 else 0)
  decreases |s|
{
  if |s| == 0 {
  } else {
    CountAppend
// </vc-code>

