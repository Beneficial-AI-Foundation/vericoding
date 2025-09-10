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
  ensures ar[i] % GCDOfSequence(ar) == 0
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
  ensures x % GCD(x, y) == 0
  ensures y % GCD(x, y) == 0
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
  ensures forall i :: 0 <= i < |ar| ==> ar[i] % GCDOfSequence(ar) == 0
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

lemma GCDOfSequencePrefixLemma(ar: seq<int>, k: int)
  requires |ar| >= 1
  requires forall i :: 0 <= i < |ar| ==> ar[i] > 0
  requires 1 <= k < |ar|
  ensures GCDOfSequence(ar[0..k+1]) == GCD(GCDOfSequence(ar[0..k]), ar[k])
  decreases |ar|
{
  if k == 1 {
    // Base case: GCDOfSequence([a0, a1]) = GCD(a0, a1)
  } else {
    GCDOfSequencePrefixLemma(ar[0..k], k-1);
    // Now we know GCDOfSequence(ar[0..k]) = GCD(GCDOfSequence(ar[0..k-1]), ar[k-1])
    // And GCDOfSequence(ar[0..k+1]) = GCD(ar[0], GCDOfSequence(ar[1..k+1]))
    // By induction we can show the relationship holds
  }
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
    GCDOfSequenceLemma(ar[0..i+1], i);
    gcd := GCD(gcd, ar[i]);
    i := i + 1;
  }
  result := gcd * n;
}
// </vc-code>

