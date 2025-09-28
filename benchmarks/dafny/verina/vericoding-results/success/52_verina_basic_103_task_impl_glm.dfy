// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
method copy_array(a: array<int>) returns (result: array<int>)
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i]
    ensures fresh(result)
{
    /* helper modified by LLM (iteration 5): fix loop bound, add loop invariant, and ensure freshness */
    result := new int[a.Length];
    for i := 0 to a.Length
        invariant forall j :: 0 <= j < i ==> result[j] == a[j]
    {
        result[i] := a[i];
    }
}
// </vc-helpers>

// <vc-spec>
method update_elements(a: array<int>) returns (result: array<int>)
    requires a.Length >= 8
    ensures result.Length == a.Length
    ensures result[4] == a[4] + 3
    ensures result[7] == 516
    ensures forall i :: 0 <= i < a.Length && i != 4 && i != 7 ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): use fixed helper that ensures freshness */
  result := copy_array(a);
  result[4] := a[4] + 3;
  result[7] := 516;
}
// </vc-code>
