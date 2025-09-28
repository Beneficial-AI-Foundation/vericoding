// <vc-preamble>
function ShiftLeftInt(x: int, shift: nat): int
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Remove duplicate function definition */
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
{
  /* code modified by LLM (iteration 4): Implement array shifting with helper function */
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == ShiftLeftInt(a[j], b[j])
  {
    result[i] := ShiftLeftInt(a[i], b[i]);
    i := i + 1;
  }
}
// </vc-code>
