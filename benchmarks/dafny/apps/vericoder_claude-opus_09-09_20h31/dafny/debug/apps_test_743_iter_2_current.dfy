predicate ValidInput(n: int, ar: seq<int>)
{
  n >= 2 && |ar| == n && forall i :: 0 <= i < n ==> ar[i] > 0
}

function GCD(x: int, y: int): int
  requires x > 0 && y > 0
  ensures GCD(x, y) > 0
  decreases if x < y then y else x
{
  if x == y then x
  else if x < y then GCD(x, y - x)
  else GCD(x - y, y)
}

function GCDOfSequence(ar: seq<int>): int
  requires |ar| >= 1
  requires forall i :: 0 <= i < |ar| ==> ar[i] > 0
  ensures GCDOfSequence(ar) > 0
  decreases |ar|
{
  if |ar| == 1 then ar[0]
  else GCD(ar[0], GCDOfSequence(ar[1..]))
}

function MinimalSum(n: int, ar: seq<int>): int
  requires ValidInput(n, ar)
{
  GCDOfSequence(ar) * n
}

// <vc-helpers>
lemma GCDPositive(x: int, y: int)
  requires x > 0 && y > 0
  ensures GCD(x, y) > 0
{
  // This follows from the ensures clause of GCD function
}

lemma GCDOfSequencePositive(ar: seq<int>)
  requires |ar| >= 1
  requires forall i :: 0 <= i < |ar| ==> ar[i] > 0
  ensures GCDOfSequence(ar) > 0
{
  // This follows from the ensures clause of GCDOfSequence function
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, ar: seq<int>) returns (result: int)
  requires ValidInput(n, ar)
  ensures result == MinimalSum(n, ar)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
  var g := ar[0];
  var i := 1;
  
  while i < n
    invariant 1 <= i <= n
    invariant g > 0
    invariant g == GCDOfSequence(ar[..i])
  {
    g := GCD(g, ar[i]);
    i := i + 1;
  }
  
  assert i == n;
  assert ar[..n] == ar;
  assert g == GCDOfSequence(ar);
  
  result := g * n;
}
// </vc-code>

