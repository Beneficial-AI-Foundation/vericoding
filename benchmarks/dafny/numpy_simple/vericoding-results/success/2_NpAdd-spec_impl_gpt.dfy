// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): retained simple addition helper for clarity */
function SumInt(x: int, y: int): int {
  x + y
}
// </vc-helpers>

// <vc-spec>
method Add(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    ensures 
        result.Length == a.Length &&
        forall i :: 0 <= i < result.Length ==> result[i] == a[i] + b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement element-wise addition with loop invariants; removed redundant null invariant */
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] + b[j]
    decreases a.Length - i
  {
    result[i] := a[i] + b[i];
    i := i + 1;
  }
}
// </vc-code>
