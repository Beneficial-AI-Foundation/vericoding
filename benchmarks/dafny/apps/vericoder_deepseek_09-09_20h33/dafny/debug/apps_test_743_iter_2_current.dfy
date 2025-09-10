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
lemma GCDOfSequenceLemma(ar: seq<int>, i: int)
  requires |ar| >= 1
  requires forall j :: 0 <= j < |ar| ==> ar[j] > 0
  requires 0 <= i < |ar|
  ensures GCDOfSequence(ar) > 0
  ensures GCDOfSequence(ar) divides ar[i]
  decreases |ar|
{
  if |ar| == 1 {
  } else {
    var gcdRest := GCDOfSequence(ar[1..]);
    if i == 0 {
      GCDDividesBoth(ar[0], gcdRest);
    } else {
      GCDOfSequenceLemma(ar[1..], i-1);
    }
  }
}

lemma GCDDividesBoth(x: int, y: int)
  requires x > 0 && y > 0
  ensures GCD(x, y) divides x
  ensures GCD(x, y) divides y
  decreases if x < y then y else x
{
  if x == y {
  } else if x < y {
    GCDDividesBoth(x, y - x);
  } else {
    GCDDividesBoth(x - y, y);
  }
}

lemma GCDOfSequenceDividesAll(ar: seq<int>)
  requires |ar| >= 1
  requires forall i :: 0 <= i < |ar| ==> ar[i] > 0
  ensures forall i :: 0 <= i < |ar| ==> GCDOfSequence(ar) divides ar[i]
  decreases |ar|
{
  if |ar| == 1 {
  } else {
    GCDOfSequenceDividesAll(ar[1..]);
    var gcdRest := GCDOfSequence(ar[1..]);
    GCDDividesBoth(ar[0], gcdRest);
  }
}

lemma GCDLemma(a: int, b: int, ar: seq<int>)
  requires a > 0 && b > 0
  requires |ar| >= 1
  requires forall i :: 0 <= i < |ar| ==> ar[i] > 0
  requires GCD(a, b) == GCDOfSequence([a] + [b] + ar)
  ensures GCD(a, GCDOfSequence([b] + ar)) == GCDOfSequence([a] + [b] + ar)
  decreases |ar|
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
  var gcd := ar[0];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant gcd > 0
    invariant gcd == GCDOfSequence(ar[0..i])
    decreases n - i
  {
    var gcdRest := GCDOfSequence(ar[0..i+1][1..]);
    GCDOfSequenceLemma(ar[0..i+1], i);
    GCDDividesBoth(gcd, ar[i]);
    gcd := GCD(gcd, ar[i]);
    i := i + 1;
  }
  result := gcd * n;
}
// </vc-code>

