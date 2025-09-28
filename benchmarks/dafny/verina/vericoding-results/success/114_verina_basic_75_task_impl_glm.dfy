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

// </vc-helpers>

// <vc-spec>
method MinArray(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> result <= a[i]
    ensures exists i :: 0 <= i < a.Length && result == a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): changed for-loop to while-loop to handle array length 1 */
  var currentMin := a[0];
  var i := 1;
  while i < a.Length
      invariant 1 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> currentMin <= a[j]
      invariant exists j :: 0 <= j < i && currentMin == a[j]
  {
      if currentMin > a[i] {
          currentMin := a[i];
      }
      i := i + 1;
  }
  result := currentMin;
}
// </vc-code>
