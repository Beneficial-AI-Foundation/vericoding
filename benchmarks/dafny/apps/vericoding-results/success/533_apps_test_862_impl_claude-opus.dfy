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
lemma ComputeCCProperties(n: int, a: seq<int>, i: int, j: int)
  requires ValidInput(n, a)
  requires 0 <= i < n && 0 <= j < n
  ensures ComputeCC(n, a, i) == n * ComputeC(n, ComputeB(a, i))
  ensures ComputeCC(n, a, j) == n * ComputeC(n, ComputeB(a, j))
{
  // This lemma helps the verifier understand the relationship
}

lemma OptimalEntranceExists(n: int, a: seq<int>, minIndex: int, minValue: int)
  requires ValidInput(n, a)
  requires 0 <= minIndex < n
  requires minValue == ComputeCC(n, a, minIndex)
  requires forall j :: 0 <= j < n ==> 
    (minValue <= ComputeCC(n, a, j) && 
     (minValue < ComputeCC(n, a, j) || minIndex <= j))
  ensures IsOptimalEntrance(n, a, minIndex + 1)
{
  // This proves that minIndex + 1 is an optimal entrance
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
  var minIndex := 0;
  var minValue := ComputeCC(n, a, 0);
  
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 0 <= minIndex < i
    invariant minValue == ComputeCC(n, a, minIndex)
    invariant forall j :: 0 <= j < i ==> 
      (minValue <= ComputeCC(n, a, j) && 
       (minValue < ComputeCC(n, a, j) || minIndex <= j))
  {
    var currentValue := ComputeCC(n, a, i);
    if currentValue < minValue {
      minValue := currentValue;
      minIndex := i;
    }
    i := i + 1;
  }
  
  assert i == n;
  assert forall j :: 0 <= j < n ==> 
    (minValue <= ComputeCC(n, a, j) && 
     (minValue < ComputeCC(n, a, j) || minIndex <= j));
  
  OptimalEntranceExists(n, a, minIndex, minValue);
  
  result := minIndex + 1;
}
// </vc-code>

