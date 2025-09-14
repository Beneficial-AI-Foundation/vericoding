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
/* helper modified by LLM (iteration 2): two-argument minimum function */
function MinOfTwo(x: int, y: int): int { if x < y then x else y }
// </vc-helpers>

// <vc-spec>
method MinArray(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> result <= a[i]
    ensures exists i :: 0 <= i < a.Length && result == a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterative min with invariants */
  var i := 1;
  var cur := a[0];
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> cur <= a[k]
    invariant exists j :: 0 <= j < i && cur == a[j]
    decreases a.Length - i
  {
    if a[i] < cur {
      cur := a[i];
    }
    i := i + 1;
  }
  result := cur;
}

// </vc-code>
