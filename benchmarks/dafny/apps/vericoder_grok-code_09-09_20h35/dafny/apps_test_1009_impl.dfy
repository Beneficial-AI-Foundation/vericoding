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

function seqContains(s: seq<int>, x: int): bool
{
  if |s| == 0 then false
  else if s[0] == x then true
  else seqContains(s[1..], x)
}

function rev(L: seq<int>): seq<int>
{
  if |L| == 0 then [] else rev(L[1..]) + [L[0]]
}

method CanPack(L: seq<int>, k: int, S: int) returns (result: bool)
  requires k >= 1
  requires forall i :: 0 <= i < |L| ==> L[i] >= 0
  requires |L| > 0 ==> S >= max(L)
  ensures result ==> exists boxes: seq<int>, items: seq<int> :: |boxes| <= k && |items| == |L| && 
            (forall i :: 0 <= i < |items| ==> 0 <= items[i] < |L| && !seqContains(items[..i], items[i]) ) &&
            ValidBoxConfiguration(boxes, S) && (forall i :: 0 <= i < |L| ==> exists j | 0 <= j < |boxes| :: seqContains(items[j..], i))
  ensures !result ==> forall boxes: seq<int> :: (|boxes| <= k && ValidBoxConfiguration(boxes, S) &&
            (forall i :: 0 <= i < |L| ==> exists j :: 0 <= j < |boxes| && boxes[j] + L[i] <= S) ) ==> false
{
  var RL := rev(L);
  var boxes: seq<int> := [];
  var i := 0;
  var placedItems := [];
  while i < |RL|
    invariant 0 <= i <= |RL|
    invariant |boxes| <= k
    invariant |placedItems| == i
    invariant forall j :: 0 <= j < |boxes| ==> 0 <= boxes[j] <= S
    invariant ValidBoxConfiguration(boxes + if |boxes| > 0 then [] else [0], S)
    invariant forall p :: 0 <= p < i ==> exists b :: 0 <= b < |boxes| ==> boxes[b] + RL[p] <= S  // temporal for simplicity
  {
    var placed := false;
    var j := 0;
    while j < |boxes| && !placed
      invariant 0 <= j <= |boxes|
      invariant !placed || (placed && 0 <= j-1 < |boxes|)
    {
      if boxes[j] + RL[i] <= S
      {
        placed := true;
        boxes := boxes[..j] + [boxes[j] + RL[i]] + boxes[j+1..];
        placedItems := placedItems + [RL[i]];
      }
      j := j + 1;
    }
    if !placed && |boxes| < k && RL[i] <= S
    {
      boxes := boxes + [RL[i]];
      placedItems := placedItems + [RL[i]];
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
    invariant low >= max(L)
    invariant high <= sum(L)
    invariant low <= high ==> !CanPack(L, k, low-1)
    invariant high >= low - 1
    invariant 0 <= high - low
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

