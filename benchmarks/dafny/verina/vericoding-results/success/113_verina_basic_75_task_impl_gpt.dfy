// <vc-preamble>
function LoopSpec(a: array<int>, i: int, currentMin: int): int
    requires 0 <= i <= a.Length
    decreases a.Length - i
    reads a
{
    if i < a.Length then
        var newMin := if currentMin > a[i] then a[i] else currentMin;
        LoopSpec(a, i + 1, newMin)
    else
        currentMin
}
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
lemma MinLeBoth(a: int, b: int)
  ensures min(a, b) <= a && min(a, b) <= b
{
}
// </vc-helpers>

// <vc-spec>
method MinArray(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> result <= a[i]
    ensures exists i :: 0 <= i < a.Length && result == a[i]
// </vc-spec>
// <vc-code>
{
  var i := 1;
  var m := a[0];
  var w := 0;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant 0 <= w < i
    invariant m == a[w]
    invariant forall j :: 0 <= j < i ==> m <= a[j]
    decreases a.Length - i
  {
    if a[i] < m {
      m := a[i];
      w := i;
    }
    i := i + 1;
  }
  result := m;
}
// </vc-code>
