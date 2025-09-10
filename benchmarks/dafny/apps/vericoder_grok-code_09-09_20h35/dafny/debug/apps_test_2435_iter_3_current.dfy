predicate ValidInput(testCases: seq<(int, int, seq<(int, int)>)>)
{
    |testCases| >= 0 &&
    forall i :: 0 <= i < |testCases| ==> 
        var (n, x, operations) := testCases[i];
        n >= 1 && 1 <= x <= n && |operations| >= 0 &&
        (forall j :: 0 <= j < |operations| ==> 
            var (l, r) := operations[j];
            1 <= l <= r <= n)
}

function computeFinalBounds(x: int, operations: seq<(int, int)>): (int, int)
    requires forall j :: 0 <= j < |operations| ==> 
        var (l, r) := operations[j];
        l <= r
{
    computeFinalBoundsHelper(x, x, operations, 0)
}

predicate ValidResults(testCases: seq<(int, int, seq<(int, int)>)>, results: seq<int>)
    requires ValidInput(testCases)
{
    |results| == |testCases| &&
    forall i :: 0 <= i < |testCases| ==> 
        var (n, x, operations) := testCases[i];
        var finalBounds := computeFinalBounds(x, operations);
        results[i] == finalBounds.1 - finalBounds.0 + 1 &&
        finalBounds.0 <= x <= finalBounds.1 &&
        results[i] >= 1 &&
        1 <= finalBounds.0 <= finalBounds.1 <= n
}

// <vc-helpers>
function IntMax(a: int, b: int): int  
  ensures result >= a && result >= b
{ 
  if a > b then a else b 
}

function IntMin(a: int, b: int): int  
  ensures result <= a && result <= b
{ 
  if a < b then a else b 
}

function computeFinalBoundsHelper(curMin: int, curMax: int, x: int, operations: seq<(int, int)>, i: int): (int, int)
  requires 0 <= i <= |operations|
  requires curMin <= x <= curMax
  requires forall j :: 0 <= j < |operations| ==> 
    var (l, r) := operations[j];
    l <= r
  decreases |operations| - i
  ensures result.0 <= x <= result.1
{
  if i == |operations| then 
    (curMin, curMax)
  else {
    var (l, r) := operations[i];
    var newMin := IntMax(curMin, l);
    var newMax := IntMin(curMax, r);
    var clampedMin := IntMin(newMin, x);
    var clampedMax := IntMax(newMax, x);
    computeFinalBoundsHelper(clampedMin, clampedMax, x, operations, i + 1)
  }
}

function computeFinalBounds(x: int, operations: seq<(int, int)>): (int, int)
  requires forall j :: 0 <= j < |operations| ==> 
    var (l, r) := operations[j];
    l <= r
  ensures result.0 <= x <= result.1
{
  computeFinalBoundsHelper(x, x, x, operations, 0)
}
// </vc-helpers>

// <vc-spec>
method solve(testCases: seq<(int, int, seq<(int, int)>)>) returns (results: seq<int>)
    requires ValidInput(testCases)
    ensures ValidResults(testCases, results)
// </vc-spec>
// <vc-code>
{
  var res := [];
  for i := 0 to |testCases| - 1 {
    var (n, x, ops) := testCases[i];
    var (mn, mx) := computeFinalBounds(x, ops);
    res := res + [mx - mn + 1];
  }
  results := res;
}
// </vc-code>

