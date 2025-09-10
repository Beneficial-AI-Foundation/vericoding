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
lemma SumAppend(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
  decreases |s|
{
  if |s| == 0 {
    // sum([x]) == x and sum([]) == 0
    assert sum([] + [x]) == x;
    assert sum([]) == 0;
  } else {
    var tl := s[1..];
    SumAppend(tl, x);
    // sum(s + [x]) = s[0] + sum(tl + [x]) = s[0] + (sum(tl) + x) = sum(s) + x
    assert sum(s + [x]) == s[0] + sum(tl + [x]);
    assert sum(s) == s[0] + sum(tl);
    assert sum(tl + [x]) == sum(tl) + x;
    assert sum(s + [x]) == s[0] + (sum(tl) + x);
    assert sum(s + [x]) == (s[0] + sum(tl)) + x;
    assert sum(s + [x]) == sum(s) + x;
  }
}

lemma CountAppend(s: seq<int>, val: int, y: int)
  ensures count(s + [y], val) == count(s, val) + (if y == val then 1 else 0)
  decreases |s|
{
  if |s| == 0 {
    // count([y], val) == (if y==val then 1 else 0) and count([]) == 0
    assert count([] + [y], val) == (if y == val then 1 else 0);
    assert count([] , val) == 0;
  } else {
    var tl := s[1..];
    CountAppend(tl, val, y);
    // count(s + [y], val) = (if s[0]==val then 1 else 0) + count(tl + [y], val)
    // = (if s[0]==val then 1 else 0) + (count(tl, val) + (if y==val then 1 else 0))
    // = count(s, val) + (if y==val then 1 else 0)
    assert count(s + [y], val) == (if s[0] == val then 1 else 0) + count(tl + [y], val);
    assert count(s, val) == (if s[0] == val then 1 else 0) + count(tl, val);
    assert count(tl + [y], val) == count(tl, val) + (if y == val then 1 else 0);
    assert count(s + [y], val) == (if s[0] == val then 1 else 0) + (count(tl, val) + (if y == val then 1 else 0));
    assert count(s + [y], val) == ((if s[0] == val then 1 else 0) + count(tl, val)) + (if y == val then 1 else 0);
    assert count(s + [y], val) == count(s, val) + (if y == val then 1 else 0);
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
    var old := result;
    if i < r {
      // append q+1
      result := old + [q + 1];
      rcount := rcount + 1;
      ssum := ssum + q + 1;
      // update sum and count facts using lemmas about append
      SumAppend(old, q + 1);
      CountAppend(old, q + 1, q + 1);
    } else {
      // append q
      result := old + [q];
      ssum := ssum + q;
      // update sum and count facts using lemmas about append
      SumAppend(old, q);
      CountAppend(old, q + 1, q); // count with respect to q+1
    }
    // Now |result| == |old| + 1 and old == result[0..|old|)
    assert |result| == |old| + 1;
    // restore element-property: existing elems from old keep their property, and the appended element is either q or q+1
    assert (forall k :: 0 <= k < |old| ==> result[k] == q || result[k] == q + 1);
    assert result[|result| - 1] == q || result[|result| - 1] == q + 1;
    // restore sum(result) == ssum: SumAppend gave sum(result) == sum(old) + appended; and ssum was updated similarly
    assert sum(result) == sum(old) + (if i < r then q + 1 else q);
    assert ssum == sum(old) + (if i < r then q + 1 else q);
    assert ssum == sum(result);
    // restore rcount == count(result, q+1) using CountAppend and previous rcount relation with old
    assert count(result, q + 1) == count(old, q + 1) + (if i < r then 1 else 0);
    // rcount was updated accordingly in each branch
    assert rcount == count(result, q + 1);
    i := i + 1;
  }
  // Post-loop checks to satisfy the ensures clause
  assert |result| == m;
  assert (forall k :: 0 <= k < |result| ==> result[k] > 0) by {
    assert q >= 1;
    // each element is q or q+1
    assert (forall k :: 0 <= k < |result| ==> result[k] == q || result[k] == q + 1);
    // hence each > 0
    var K := |result|;
    assert (forall k :: 0 <= k < K ==> result[k] > 0);
  }
  // sum(result) == q*m + rcount and n == q*m + r, so rcount == r and sum == n
  assert ssum == q * m + rcount;
  assert n == q * m + r;
  assert ssum == n;
  assert count(result, q + 1) == r;
  assert count(result, q) == m - r;
}
// </vc-code>

