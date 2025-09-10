predicate ValidInput(n: int, k: int, L: seq<int>)
{
    n >= 1 && k >= 1 && n <= 2*k &&
    |L| == n &&
    (forall i :: 0 <= i < |L|-1 ==> L[i] <= L[i+1]) &&
    (forall i :: 0 <= i < |L| ==> L[i] >= 0)
}

predicate ValidBoxConfiguration(boxes: seq<int>, boxSize: int)
{
    |boxes| >= 1 &&
    (forall i :: 0 <= i < |boxes| ==> boxes[i] <= boxSize) &&
    (forall i :: 0 <= i < |boxes| ==> boxes[i] >= 0)
}

function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

function max(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= max(s[1..]) then s[0]
    else max(s[1..])
}

// <vc-helpers>
predicate ValidBoxConfiguration(boxes: seq<int>, boxSize: int)
{
    |boxes| >= 1 &&
    (forall i :: 0 <= i < |boxes| ==> boxes[i] <= boxSize) &&
    (forall i :: 0 <= i < |boxes| ==> boxes[i] >= 0)
}

function rev(L: seq<int>): seq<int>
{
  if |L| == 0 then [] else rev(L[1..]) + [L[0]]
}

method CanPack(L: seq<int>, k: int, S: int): bool
  requires k >= 1
  requires forall i :: 0 <= i < |L| ==> L[i] >= 0
  requires |L| > 0 ==> S >= max(L)
  ensures false
{
  var RL := rev(L);
  var boxes: seq<int> := [];
  var i := 0;
  while i < |RL|
  {
    var placed := false;
    var j := 0;
    while j < |boxes| && !placed
    {
      if boxes[j] + RL[i] <= S
      {
        placed := true;
        boxes := boxes[..j] + [boxes[j] + RL[i]] + boxes[j+1..];
      }
      j := j + 1;
    }
    if !placed && |boxes| < k && RL[i] <= S
    {
      boxes := boxes + [RL[i]];
    }
    else if !placed
    {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, L: seq<int>) returns (result: int)
    requires ValidInput(n, k, L)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var low := max(L);
  var high := sum(L);
  while low <= high
  {
    var mid := (low + high) / 2;
    if CanPack(L, k, mid)
    {
      high := mid - 1;
    }
    else
    {
      low := mid + 1;
    }
  }
  return low;
}
// </vc-code>

