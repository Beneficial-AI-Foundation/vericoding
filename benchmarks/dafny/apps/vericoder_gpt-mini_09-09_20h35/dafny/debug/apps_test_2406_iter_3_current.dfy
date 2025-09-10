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
  assert q >= 0;
  var a := new int[n];
  var i := 0;
  while i < n - r
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == q
    decreases n - i
  {
    a[i] := q;
    i := i + 1;
  }
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
    s := s + a[i];
    i := i + 1;
  }
  result := a[..];
  assert |result| == n;
  assert forall i2 :: 0 <= i2 < n ==> result[i2] >= 0;
  assert forall i2 :: 0 <= i2 < n-1 ==> result[i2] <= result[i2+1];
  assert forall i2 :: 0 <= i2 < n-1 ==> result[i2+1] - result[i2] <= 1;
  assert s == S;
  assert sum_seq(result) == S;
  assert IsStable(result);
}
// </vc-code>

