// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CubeElements(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == a[i] * a[i] * a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed syntax error in forall loop */
  result := new int[a.Length];
  forall i | 0 <= i < a.Length {
    result[i] := a[i] * a[i] * a[i];
  }
}
// </vc-code>
