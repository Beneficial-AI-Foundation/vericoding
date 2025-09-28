// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method multiply(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i] * b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added loop invariant and ensures result correctness, fixed loop bounds */
  var n := a.Length;
  result := new int[n];
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] * b[k]
    decreases n - i
  {
    result[i] := a[i] * b[i];
    i := i + 1;
  }
}
  
// </vc-code>
