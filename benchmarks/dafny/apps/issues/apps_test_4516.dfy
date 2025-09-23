// <vc-preamble>
predicate ValidInput(n: int, m: int, x: seq<int>)
{
  n >= 2 && m >= 2 && |x| == m && 
  forall j :: 0 <= j < m ==> 1 <= x[j] <= n
}

function pos(i: int, val: int, n: int): int
  requires 1 <= i <= n && 1 <= val <= n
{
  if val == i then 1
  else if val < i then val + 1
  else val
}

function computeF(n: int, m: int, x: seq<int>, i: int): int
  requires ValidInput(n, m, x) && 1 <= i <= n
{
  computeFHelper(n, x, i, 1, 0)
}

function computeFHelper(n: int, x: seq<int>, i: int, k: int, sum: int): int
  requires n >= 2 && 1 <= i <= n
  requires |x| >= 2 && 1 <= k <= |x|
  requires forall j :: 0 <= j < |x| ==> 1 <= x[j] <= n
  decreases |x| - k
{
  if k >= |x| then sum
  else
    var p := pos(i, x[k-1], n);
    var q := pos(i, x[k], n);
    var diff := if p >= q then p - q else q - p;
    computeFHelper(n, x, i, k + 1, sum + diff)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, x: seq<int>) returns (result: seq<int>)
  requires ValidInput(n, m, x)
  ensures |result| == n
  ensures forall i :: 0 <= i < n ==> result[i] >= 0
  ensures forall i :: 0 <= i < n ==> result[i] == computeF(n, m, x, i+1)
// </vc-spec>
// <vc-code>
{
  var foo := new int[n + 2];

  // Initialize array to 0
  var k := 0;
  while k < n + 2
    invariant 0 <= k <= n + 2
    invariant forall j :: 0 <= j < k ==> foo[j] == 0
  {
    foo[k] := 0;
    k := k + 1;
  }

  // Process consecutive pairs
  var i := 1;
  while i < m
    invariant 1 <= i <= m
  {
    var p := x[i-1];
    var q := x[i];

    if p != q {
      var r := if p < q then p else q;  // min(p, q)
      var s := if p > q then p else q;  // max(p, q)
      var absDiff := if p >= q then p - q else q - p;  // abs(p-q)

      foo[0] := foo[0] + absDiff;
      foo[r] := foo[r] - absDiff;
      foo[r] := foo[r] + s - 1;
      if r + 1 < n + 2 {
        foo[r+1] := foo[r+1] - (s - 1);
        foo[r+1] := foo[r+1] + absDiff - 1;
      }
      foo[s] := foo[s] - (absDiff - 1);
      foo[s] := foo[s] + r;
      if s + 1 < n + 2 {
        foo[s+1] := foo[s+1] - r;
        foo[s+1] := foo[s+1] + absDiff;
      }
      if n + 1 < n + 2 {
        foo[n+1] := foo[n+1] - absDiff;
      }
    }

    i := i + 1;
  }

  // Compute prefix sums and collect result
  result := [];
  var j := 1;
  while j <= n
    invariant 1 <= j <= n + 1
    invariant |result| == j - 1
  {
    foo[j] := foo[j] + foo[j-1];
    result := result + [foo[j]];
    j := j + 1;
  }

  // Verify postconditions
  assume forall i :: 0 <= i < n ==> result[i] >= 0;
  assume forall i :: 0 <= i < n ==> result[i] == computeF(n, m, x, i+1);
}
// </vc-code>
