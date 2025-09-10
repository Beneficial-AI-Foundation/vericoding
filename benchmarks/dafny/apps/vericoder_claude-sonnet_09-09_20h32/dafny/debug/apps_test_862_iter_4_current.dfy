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

// <vc-helpers>
lemma ComputeCCMonotonicity(n: int, a: seq<int>, i: int, j: int)
  requires ValidInput(n, a) && 0 <= i < n && 0 <= j < n
  requires ComputeCC(n, a, i) < ComputeCC(n, a, j)
  ensures forall k :: 0 <= k < n ==> 
    (var cci := ComputeCC(n, a, i);
     var cck := ComputeCC(n, a, k);
     cci <= cck && (cci < cck || i <= k)) || 
    (var ccj := ComputeCC(n, a, j);
     var cck := ComputeCC(n, a, k);
     ccj <= cck && (ccj < cck || j <= k))
{
  var cci := ComputeCC(n, a, i);
  var ccj := ComputeCC(n, a, j);
  
  forall k | 0 <= k < n
    ensures (var cck := ComputeCC(n, a, k);
             cci <= cck && (cci < cck || i <= k)) || 
            (var cck := ComputeCC(n, a, k);
             ccj <= cck && (ccj < cck || j <= k))
  {
    var cck := ComputeCC(n, a, k);
    if cci <= ccj && ccj <= cck {
      assert cci <= cck && (cci < cck || i <= k);
    } else if cci <= cck {
      assert cci <= cck && (cci < cck || i <= k);
    } else {
      assert ccj <= cck && (ccj < cck || j <= k);
    }
  }
}

lemma OptimalEntranceExists(n: int, a: seq<int>)
  requires ValidInput(n, a)
  ensures exists entrance :: 1 <= entrance <= n && IsOptimalEntrance(n, a, entrance)
{
  var minCC := ComputeCC(n, a, 0);
  var minIdx := 0;
  
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 0 <= minIdx < i
    invariant minCC == ComputeCC(n, a, minIdx)
    invariant forall j :: 0 <= j < i ==> 
      (ComputeCC(n, a, minIdx) <= ComputeCC(n, a, j) && 
       (ComputeCC(n, a, minIdx) < ComputeCC(n, a, j) || minIdx <= j))
  {
    var currentCC := ComputeCC(n, a, i);
    if currentCC < minCC || (currentCC == minCC && i < minIdx) {
      minCC := currentCC;
      minIdx := i;
    }
    i := i + 1;
  }
  
  assert IsOptimalEntrance(n, a, minIdx + 1);
}

lemma OptimalEntranceCorrectness(n: int, a: seq<int>, minIdx: int)
  requires ValidInput(n, a) && 0 <= minIdx < n
  requires forall j :: 0 <= j < n ==> 
    (ComputeCC(n, a, minIdx) <= ComputeCC(n, a, j) && 
     (ComputeCC(n, a, minIdx) < ComputeCC(n, a, j) || minIdx <= j))
  ensures IsOptimalEntrance(n, a, minIdx + 1)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
  requires ValidInput(n, a)
  ensures 1 <= result <= n
  ensures IsOptimalEntrance(n, a, result)
// </vc-spec>
// <vc-code>
{
  var minCC := ComputeCC(n, a, 0);
  var minIdx := 0;
  
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 0 <= minIdx < i
    invariant minCC == ComputeCC(n, a, minIdx)
    invariant forall j :: 0 <= j < i ==> 
      (ComputeCC(n, a, minIdx) <= ComputeCC(n, a, j) && 
       (ComputeCC(n, a, minIdx) < ComputeCC(n, a, j) || minIdx <= j))
  {
    var currentCC := ComputeCC(n, a, i);
    if currentCC < minCC || (currentCC == minCC && i < minIdx) {
      minCC := currentCC;
      minIdx := i;
    }
    i := i + 1;
  }
  
  OptimalEntranceCorrectness(n, a, minIdx);
  result := minIdx + 1;
}
// </vc-code>

