// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): noop lemma retained for potential future helpers */
lemma Helpers_Noop() ensures true {
}

// </vc-helpers>

// <vc-spec>
method Find(a: array<int>, key: int) returns (result: int)
    ensures
        (result == -1 || (result >= 0 && result < a.Length)) &&
        (result != -1 ==> (a[result] == key && forall i :: 0 <= i < result ==> a[i] != key)) &&
        (result == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != key)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): linear search with corrected loop invariants (no trailing semicolons) */
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != key
  {
    if a[i] == key {
      result := i;
      return;
    }
    i := i + 1;
  }
  result := -1;
}
// </vc-code>
