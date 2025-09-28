// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple integer <= helper retained for clarity */
function le(x: int, y: int): bool {
  x <= y
}
// </vc-helpers>

// <vc-spec>
method LessEqual(a: array<int>, b: array<int>) returns (result: array<bool>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == (a[i] <= b[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): remove null invariants and implement element-wise <= */
  var n := a.Length;
  result := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a.Length == n && b.Length == n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == (a[j] <= b[j])
  {
    result[i] := (a[i] <= b[i]);
    i := i + 1;
  }
}
// </vc-code>
