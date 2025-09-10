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
function max(a: int, b: int): int {
    if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: seq<int>) returns (result: int)
    requires ValidInput(n, m)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var prev := m[0] + 1;
  var i := 1;
  var sum := 0;
  while i < n
      invariant 1 <= i <= n
      invariant sum >= 0
      invariant prev >= m[i-1] + 1
  {
      prev := max(prev, m[i] + 1);
      sum := sum + prev - 1 - m[i];
      i := i + 1;
  }
  return sum;
}
// </vc-code>

