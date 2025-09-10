predicate ValidInput(n: int, heights: seq<int>)
{
    n > 0 && |heights| == n &&
    (forall i :: 0 <= i < n ==> heights[i] >= 0) &&
    (forall i :: 0 <= i < n-1 ==> heights[i] < heights[i+1])
}

predicate ValidOutput(n: int, result: seq<int>)
{
    |result| == n &&
    (forall i :: 0 <= i < n ==> result[i] >= 0) &&
    (forall i :: 0 <= i < n-1 ==> result[i] <= result[i+1]) &&
    (forall i :: 0 <= i < n-1 ==> result[i+1] - result[i] <= 1)
}

predicate IsStable(result: seq<int>)
{
    forall i :: 0 <= i < |result|-1 ==> !(result[i] + 2 <= result[i+1])
}

function sum_seq(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum_seq(s[1..])
}

// <vc-helpers>
function sum_sq(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0]*s[0] + sum_sq(s[1..])
}

lemma SumSeqNonneg(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures sum_seq(s) >= 0
  decreases |s|
{
  if |s| > 0 {
    SumSeqNonneg(s[1..]);
    assert sum_seq(s) == s[0] + sum_seq(s[1..]);
    assert s[0] + sum_seq(s[1..]) >= 0;
  }
}

lemma SumAllSame(s: seq<int>, c: int)
  requires forall i :: 0 <= i < |s| ==> s[i] == c
  ensures sum_seq(s) == c * |s|
  decreases |s|
{
  if |s| > 0 {
    SumAllSame(s[1..], c);
    assert sum_seq(s) == s[0] + sum_seq(s[1..]);
    assert s[0] == c;
    assert sum_seq(s[1..]) == c * |s[1..]|;
    assert sum_seq(s) == c + c * |s[1..]|;
    assert sum_seq(s) == c * |s|;
  }
}

lemma SumConcat(s: seq<int>, t: seq<int>)
  ensures sum_seq(s + t) == sum_seq(s) + sum_seq(t)
  decreases |s|
{
  if |s| > 0 {
    // (s + t)[1..] == s[1..] + t
    SumConcat(s[1..], t);
    assert sum_seq(s + t) == (s + t)[0] + sum_seq((s + t)[1..]);
    assert (s + t)[0] == s[0];
    assert (s + t)[1..] == s[1..] + t;
    assert sum_seq((s + t)[1..]) == sum_seq(s[1..] + t);
    assert sum_seq(s[1..] + t) == sum_seq(s[1..]) + sum_seq(t);
    assert sum_seq(s + t) == s[0] + (sum_seq(s[1..]) + sum_seq(t));
    assert sum_seq(s + t) == (s[0] + sum_seq(s[1..])) + sum_seq(t);
    assert sum_seq(s + t) == sum_seq(s) + sum_seq(t);
  } else {
    // s is empty
    assert s + t == t;
    assert sum_seq(s + t) == sum_seq(t);
    assert sum_seq(s) == 0;
    assert sum_seq(s + t) == sum_seq(s) + sum_seq(t);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, heights)
    ensures ValidOutput(n, result)
    ensures sum_seq(result) == sum_seq(heights)
    ensures IsStable(result)
// </vc-spec>
// <vc-code>
{
  var S := sum_seq(heights);
  var q := S / n;
  var r := S % n;
  assert n > 0;
  SumSeqNonneg(heights);
  assert S >= 0;
  assert 0 <= r < n;
  assert S == q * n + r;
  assert q >= 0;
  var a := new int[n];
  var k := 0;
  while k < n - r
    invariant 0 <= k <= n
    invariant forall j :: 0 <= j < k ==> a[j] == q
    decreases n - k
  {
    a[k] := q;
    k := k + 1;
  }
  assert forall j :: 0 <= j < n - r ==> a[j] == q;
  var i := n - r;
  while i < n
    invariant n - r <= i <= n
    invariant forall j :: 0 <= j < n - r ==> a[j] == q
    invariant forall j :: n - r <= j < i ==> a[j] == q + 1
    decreases n - i
  {
    a[i] := q + 1;
    i := i + 1;
  }
  var s := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == sum_seq(a[..i])
    decreases n - i
  {
    s := sum_seq(a[..i+1]);
    i := i + 1;
  }
  result := a[..];
  assert |result| == n;
  assert forall i2 :: 0 <= i2 < n ==> result[i2] >= 0;
  assert forall i2 :: 0 <= i2 < n-1 ==> result[i2] <= result[i2+1];
  assert forall i2 :: 0 <= i2 < n-1 ==> result[i2+1] - result[i2] <= 1;

  // Prove sum equality using the known structure of a
  var left := a[..n - r];
  var right := a[n - r..];
  // elements are constant on slices by the loop invariants above
  assert forall k2 :: 0 <= k2 < |left| ==> left[k2] == q;
  assert forall k2 :: 0 <= k2 < |right| ==> right[k2] == q + 1;
  SumAllSame(left, q);
  SumAllSame(right, q + 1);
  SumConcat(left, right);
  assert result == left + right;
  assert sum_seq(result) == sum_seq(left + right);
  assert sum_seq(result) == sum_seq(left) + sum_seq(right);
  assert sum_seq(result) == q * |left| + (q + 1) * |right|;
  assert |left| == n - r;
  assert |right| == r;
  assert sum_seq(result) == q * (n - r) + (q + 1) * r;
  assert sum_seq(result) == q * n + r;
  assert sum_seq(result) == S;
  assert s == S;
  assert IsStable(result);
}
// </vc-code>

