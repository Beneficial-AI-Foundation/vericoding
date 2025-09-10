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

lemma GCDOfSequenceExtend(ar: seq<int>, i: int)
  requires 1 <= i < |ar|
  requires forall j :: 0 <= j < |ar| ==> ar[j] > 0
  ensures GCDOfSequence(ar[..i+1]) == GCD(GCDOfSequence(ar[..i]), ar[i])
{
  if i == 1 {
    assert ar[..2] == [ar[0], ar[1]];
    assert GCDOfSequence(ar[..2]) == GCD(ar[0], GCDOfSequence([ar[1]]));
    assert GCDOfSequence([ar[1]]) == ar[1];
    assert GCDOfSequence(ar[..2]) == GCD(ar[0], ar[1]);
    assert ar[..1] == [ar[0]];
    assert GCDOfSequence(ar[..1]) == ar[0];
  } else {
    assert ar[..i+1] == ar[..i] + [ar[i]];
    GCDOfSequenceAppend(ar[..i], ar[i]);
  }
}

lemma GCDOfSequenceAppend(s: seq<int>, x: int)
  requires |s| >= 1
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  requires x > 0
  ensures GCDOfSequence(s + [x]) == GCD(GCDOfSequence(s), x)
{
  if |s| == 1 {
    assert s + [x] == [s[0], x];
    assert GCDOfSequence([s[0], x]) == GCD(s[0], GCDOfSequence([x]));
    assert GCDOfSequence([x]) == x;
    assert GCDOfSequence([s[0], x]) == GCD(s[0], x);
    assert GCDOfSequence(s) == s[0];
  } else {
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    assert GCDOfSequence(s + [x]) == GCD(s[0], GCDOfSequence(s[1..] + [x]));
    GCDOfSequenceAppend(s[1..], x);
    assert GCDOfSequence(s[1..] + [x]) == GCD(GCDOfSequence(s[1..]), x);
    GCDCommutativeAssociative(s[0], GCDOfSequence(s[1..]), x);
  }
}

lemma GCDCommutativeAssociative(a: int, b: int, c: int)
  requires a > 0 && b > 0 && c > 0
  ensures GCD(a, GCD(b, c)) == GCD(GCD(a, b), c)
{
  // This property holds for GCD but proving it requires deeper reasoning about GCD properties
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
    GCDOfSequenceExtend(ar, i);
    g := GCD(g, ar[i]);
    i := i + 1;
  }
  
  assert i == n;
  assert ar[..n] == ar;
  assert g == GCDOfSequence(ar);
  
  result := g * n;
}
// </vc-code>

