// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method how_many_times(s: string, substr: string) returns (times: int)

    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added an assertion to guide the verifier on set cardinality */
  times := 0;
  if |s| < |substr| {
    return;
  }
  var i := 0;
  while i <= |s| - |substr|
    invariant 0 <= i <= |s| - |substr| + 1
    invariant times == |set j | 0 <= j < i && s[j..j+|substr|] == substr|
  {
    // This assertion helps Dafny prove the inductive step of the loop invariant.
    // It establishes the relationship between the number of occurrences up to i (exclusive)
    // and the number of occurrences up to i+1 (exclusive).
    assert |(set j | 0 <= j < i + 1 && s[j..j+|substr|] == substr)| ==
           |(set j | 0 <= j < i && s[j..j+|substr|] == substr)| + 
           (if s[i..i+|substr|] == substr then 1 else 0);

    if s[i..i+|substr|] == substr {
      times := times + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
