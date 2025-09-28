// <vc-preamble>
function ShiftLeftInt(x: int, shift: nat): int
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed duplicate function definition. The function is defined in vc-preamble, so no need to redefine it here. */
// </vc-helpers>

// <vc-spec>
method LeftShift(a: array<int>, b: array<nat>) returns (result: array<int>)
    requires 
        a.Length == b.Length &&
        forall i :: 0 <= i < b.Length ==> b[i] < 64
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < result.Length ==> result[i] == ShiftLeftInt(a[i], b[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implemented array creation and element-wise left shift using a forall loop. */
{
  var n := a.Length;
  result := new int[n];
  forall i | 0 <= i < n {
    result[i] := ShiftLeftInt(a[i], b[i]);
  }
}
// </vc-code>
