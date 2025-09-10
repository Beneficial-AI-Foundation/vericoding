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
    CountAppendOne(s[1..], val, x);
    assert count(s + [x], val) == (if (s + [x])[0] == val then 1 else 0) + count((s + [x])[1..], val);
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    assert count(s, val) == (if s[0] == val then 1 else 0) + count(s[1..], val);
  }
}
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
  assert q >= 1;
  assert 0 <= r < m;

  var result: seq<int> := [];
  var i := 0;
  var t := 0;

  while i < m
    invariant 0 <= i <= m
    invariant |result| == i
    invariant 0 <= r < m
    invariant 0 <= t <= r
    invariant t == (if i <= r then i else r)
    invariant q >= 1
    invariant sum(result) == i * q + t
    invariant forall k :: 0 <= k < |result| ==> result[k] == q || result[k] == q + 1
    invariant count(result, q) == i - t
    invariant count(result, q + 1) == t
    decreases m - i
  {
    var prev := result;
    if t < r {
      result := prev + [q + 1];

      // sum update
      SumAppendOne(prev, q + 1);
      assert sum(result) == sum(prev + [q + 1]);
      assert sum(result) == sum(prev) + (q + 1);
      assert sum(result) == i * q + t + q + 1;

      // counts update
      CountAppendOne(prev, q, q + 1);
      assert count(result, q) == count(prev + [q + 1], q);
      assert count(result, q) == count(prev, q) + 0;
      CountAppendOne(prev, q + 1, q + 1);
      assert count(result, q + 1) == count(prev + [q + 1], q + 1);
      assert count(result, q + 1) == count(prev, q + 1) + 1;

      // shape update
      assert |result| == |prev| + 1;
      assert forall k :: 0 <= k < |result| ==> result[k] == q || result[k] == q + 1 {
        forall k | 0 <= k < |result| {
          if k < |prev| {
            assert result[k] == prev[k];
          } else {
            assert k == |prev|;
            assert result[k] == q + 1;
          }
        }
      }

      i := i + 1;
      t := t + 1;

      // re-establish sum relation compactly
      assert sum(result) == i * q + t;

    } else {
      // here t == r
      result := prev + [q];

      // sum update
      SumAppendOne(prev, q);
      assert sum(result) == sum(prev + [q]);
      assert sum(result) == sum(prev) + q;
      assert sum(result) == i * q + t + q;

      // counts update
      CountAppendOne(prev, q, q);
      assert count(result, q) == count(prev + [q], q);
      assert count(result, q) == count(prev, q) + 1;
      CountAppendOne(prev, q + 1
// </vc-code>

