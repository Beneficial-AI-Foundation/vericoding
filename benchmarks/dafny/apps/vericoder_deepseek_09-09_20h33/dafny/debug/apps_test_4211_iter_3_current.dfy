predicate ValidInput(n: int, b: seq<int>)
{
  n >= 2 && |b| == n - 1 && forall i :: 0 <= i < |b| ==> b[i] >= 0
}

predicate CorrectResult(n: int, b: seq<int>, result: int)
  requires ValidInput(n, b)
{
  if n == 2 then
    result == 2 * b[0]
  else
    result == b[0] + b[n-2] + sum_mins(b, n-2)
}

// <vc-helpers>
function sum_mins(b: seq<int>, k: int): int
  requires |b| >= k && k >= 0
  requires forall i :: 0 <= i < |b| ==> b[i] >= 0
  decreases k
{
  if k == 0 then
    0
  else if |b| == 0 then
    0
  else
    sum_mins(b[1..], k-1) + b[0]
}

lemma sum_mins_property(b: seq<int>, k: int)
  requires |b| >= k && k >= 0
  requires forall i :: 0 <= i < |b| ==> b[i] >= 0
  ensures sum_mins(b, k) == sum_mins(b[1..], k-1) + (if k > 0 && |b| > 0 then b[0] else 0)
  decreases k
{
  if k > 0 && |b| > 0 {
    if k == 1 {
      // Trivial case
    } else {
      sum_mins_property(b[1..], k-1);
    }
  }
}

lemma sum_mins_tail_property(b: seq<int>, k: int)
  requires |b| >= k && k >= 0
  requires forall i :: 0 <= i < |b| ==> b[i] >= 0
  ensures sum_mins(b[1..], k) == (if |b| > 0 && k <= |b| - 1 then sum_mins(b[1..], k) else 0)
{
}

lemma sum_mins_length_property(b: seq<int>, k: int)
  requires |b| >= k && k >= 0
  requires forall i :: 0 <= i < |b| ==> b[i] >= 0
  ensures |b[1..]| == |b| - 1
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, b: seq<int>) returns (result: int)
  requires ValidInput(n, b)
  ensures CorrectResult(n, b, result)
// </vc-spec>
// <vc-code>
{
  if n == 2 {
    result := 2 * b[0];
  } else {
    var left := b[0];
    var right := b[n-2];
    var inner_b := b[1..];
    assert |inner_b| == n-2;
    assert forall i :: 0 <= i < |inner_b| ==> inner_b[i] >= 0;
    var inner := solve(n-1, inner_b);
    result := left + right + inner;
  }
}
// </vc-code>

