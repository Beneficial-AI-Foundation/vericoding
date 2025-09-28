// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NotEqual(a: array<int>, b: array<int>) returns (result: array<bool>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == (a[i] != b[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed duplicate variable name by using 'res' for local array and added loop invariants for verification */
  var res := new bool[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant res.Length == a.Length
    invariant forall k :: 0 <= k < i ==> res[k] == (a[k] != b[k])
  {
    res[i] := a[i] != b[i];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
