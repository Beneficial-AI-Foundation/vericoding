Allen starts at the end of queue 1 and moves cyclically through n queues.
Each minute, one person from each non-empty queue enters the fan zone.
If Allen is at the front of his current queue, he enters; otherwise he moves to the next queue.
Find which entrance Allen will use to enter the fan zone.

predicate ValidInput(n: int, a: seq<int>) {
  n >= 2 && |a| == n && (forall i :: 0 <= i < n ==> a[i] >= 0)
}

function ComputeB(a: seq<int>, i: int): int
  requires 0 <= i < |a|
{
  a[i] - i
}

function ComputeC(n: int, b: int): int
  requires n >= 2
{
  if b < 0 then b / n else (b + n - 1) / n
}

function ComputeCC(n: int, a: seq<int>, i: int): int
  requires ValidInput(n, a) && 0 <= i < n
{
  var b := ComputeB(a, i);
  var c := ComputeC(n, b);
  n * c
}

predicate IsOptimalEntrance(n: int, a: seq<int>, entrance: int)
  requires ValidInput(n, a) && 1 <= entrance <= n
{
  var i := entrance - 1;
  forall j :: 0 <= j < n ==> 
    (var cci := ComputeCC(n, a, i);
     var ccj := ComputeCC(n, a, j);
     cci <= ccj && (cci < ccj || i <= j))
}

method solve(n: int, a: seq<int>) returns (result: int)
  requires ValidInput(n, a)
  ensures 1 <= result <= n
  ensures IsOptimalEntrance(n, a, result)
{
  var b0 := a[0] - 0;
  var c0: int;
  if b0 < 0 {
    c0 := b0 / n;
  } else {
    c0 := (b0 + n - 1) / n;
  }
  var mn := n * c0;
  var ans := 1;

  for i := 0 to n 
    invariant 1 <= ans <= n
    invariant ans <= i + 1
    invariant exists k :: 0 <= k < n && ans == k + 1 && 
      (var bk := a[k] - k;
       var ck := if bk < 0 then bk / n else (bk + n - 1) / n;
       var cck := n * ck;
       mn == cck)
    invariant forall k :: 0 <= k < i ==> 
      (var bk := a[k] - k;
       var ck := if bk < 0 then bk / n else (bk + n - 1) / n;
       var cck := n * ck;
       mn <= cck && (mn < cck || (ans - 1) <= k))
  {
    var b := a[i] - i;
    var c: int;
    if b < 0 {
      c := b / n;
    } else {
      c := (b + n - 1) / n;
    }
    var cc := n * c;

    if cc < mn || (cc == mn && i < ans - 1) {
      mn := cc;
      ans := i + 1;
    }
  }

  result := ans;
}
