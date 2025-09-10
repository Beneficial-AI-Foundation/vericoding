predicate ValidInput(n: int, m: seq<int>) {
    n > 0 && |m| == n && 
    forall i :: 0 <= i < n ==> 0 <= m[i] < i + 1
}

predicate ValidSolution(n: int, m: seq<int>, dm: seq<int>) {
    |dm| == n && |m| == n &&
    (forall i :: 0 <= i < n ==> dm[i] >= m[i] + 1) &&
    (forall i :: 0 <= i < n - 1 ==> dm[i] <= dm[i + 1])
}

function SumBelow(m: seq<int>, dm: seq<int>): int
    requires |m| == |dm|
{
    if |m| == 0 then 0
    else (dm[0] - 1 - m[0]) + SumBelow(m[1..], dm[1..])
}

// <vc-helpers>
lemma SumBelowNonNegative(m: seq<int>, dm: seq<int>)
  requires |m| == |dm|
  requires forall i :: 0 <= i < |m| ==> dm[i] >= m[i] + 1
  requires forall i :: 0 <= i < |m| - 1 ==> dm[i] <= dm[i + 1]
  ensures SumBelow(m, dm) >= 0
{
  if |m| > 0 {
    var inner_m := m[1..];
    var inner_dm := dm[1..];
    
    assert dm[0] - 1 - m[0] >= 0;
    
    SumBelowNonNegative(inner_m, inner_dm);
  }
}

function max(a: int, b: int): int
{
  if a >= b then a else b
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: seq<int>) returns (result: int)
    requires ValidInput(n, m)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var dm := new int[n];
  var sum := 0;
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant dm.Length == n
    invariant forall j :: 0 <= j < i ==> dm[j] >= m[j] + 1
    invariant forall j :: 0 <= j < i - 1 ==> dm[j] <= dm[j + 1]
    invariant SumBelow(m[0..i], dm[0..i]) >= 0
  {
    dm[i] := max(m[i] + 1, if i > 0 then dm[i-1] else 0);
    sum := sum + (dm[i] - 1 - m[i]);
    i := i + 1;
  }
  
  result := sum;
}
// </vc-code>

