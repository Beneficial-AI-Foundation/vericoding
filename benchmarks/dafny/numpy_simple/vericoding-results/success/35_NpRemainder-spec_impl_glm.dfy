// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method remainder(a: array<int>, b: array<int>) returns (result: array<int>)
    requires 
        a.Length == b.Length
    requires
        forall i :: 0 <= i < b.Length ==> b[i] != 0
    ensures
        result.Length == a.Length
    ensures
        forall i :: 0 <= i < result.Length ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed loop bounds and initialization */
{
  result := new int[a.Length];
  for i := 0 to a.Length
      invariant forall j :: 0 <= j < i ==> result[j] == a[j] % b[j]
  {
      if i < a.Length {
          result[i] := a[i] % b[i];
      }
  }
}
// </vc-code>
