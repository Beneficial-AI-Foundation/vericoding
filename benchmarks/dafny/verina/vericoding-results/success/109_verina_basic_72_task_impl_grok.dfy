// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Append(a: array<int>, b: int) returns (result: array<int>)
    ensures result.Length == a.Length + 1
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i]
    ensures result[a.Length] == b
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added reads clause and full bounds check to lambda to fix reads and index errors */
  result := new int[a.Length + 1] ((i: int) reads a => if 0 <= i < a.Length then a[i] else b);
}
// </vc-code>
