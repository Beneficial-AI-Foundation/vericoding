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
function ComputeGCD(x: int, y: int): int
  requires x > 0 && y > 0
  ensures ComputeGCD(x, y) > 0
  ensures ComputeGCD(x, y) == GCD(x, y)
  decreases if x < y then y else x
{
  if x == y then x
  else if x < y then ComputeGCD(x, y - x)
  else ComputeGCD(x - y, y)
}

function ComputeGCDOfSequence(ar: seq<int>): int
  requires |ar| >= 1
  requires forall i :: 0 <= i < |ar| ==> ar[i] > 0
  ensures ComputeGCDOfSequence(ar) > 0
  ensures ComputeGCDOfSequence(ar) == GCDOfSequence(ar)
  decreases |ar|
{
  if |ar| == 1 then ar[0]
  else ComputeGCD(ar[0], ComputeGCDOfSequence(ar[1..]))
}

lemma GCDPositive(x: int, y: int)
  requires x > 0 && y > 0
  ensures GCD(x, y) > 0
{
}

lemma GCDOfSequencePositive(ar: seq<int>)
  requires |ar| >= 1
  requires forall i :: 0 <= i < |ar| ==> ar[i] > 0
  ensures GCDOfSequence(ar) > 0
{
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
  var gcd := ComputeGCDOfSequence(ar);
  result := gcd * n;
}
// </vc-code>

