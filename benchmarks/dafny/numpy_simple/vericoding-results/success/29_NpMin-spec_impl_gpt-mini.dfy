// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): integer minimum helper */
function minInt(x: int, y: int): int
{
  if x <= y then x else y
}
// </vc-helpers>

// <vc-spec>
method min(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && result == a[i]
    ensures forall i :: 0 <= i < a.Length ==> result <= a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): simple iterative scan for minimum */
  var minVal := a[0];
  var i := 1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant exists j :: 0 <= j < i && minVal == a[j]
    invariant forall k :: 0 <= k < i ==> minVal <= a[k]
  {
    if a[i] < minVal {
      minVal := a[i];
    }
    i := i + 1;
  }
  result := minVal;
}
// </vc-code>
