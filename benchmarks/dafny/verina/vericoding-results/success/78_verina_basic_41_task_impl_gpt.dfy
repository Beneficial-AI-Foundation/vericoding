// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): bind i and j using a forall-statement inside the proof to avoid unresolved identifiers */
lemma AllEqualToImpliesPairwise(a: array<int>, v: int)
  requires forall t :: 0 <= t < a.Length ==> a[t] == v
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
{
  assert forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j] by {
    forall i, j | 0 <= i < a.Length && 0 <= j < a.Length
      ensures a[i] == a[j]
    {
      assert a[i] == v;
      assert a[j] == v;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result ==> (forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j])
    ensures !result ==> (exists i :: 0 <= i < a.Length && a[i] != a[0])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): iterate to check all elements equal; on mismatch prove existential; on success use helper lemma for pairwise equality */
  var v := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i
    invariant i <= a.Length
    invariant forall t :: 0 <= t < i ==> a[t] == v
    decreases a.Length - i
  {
    if a[i] == v {
      i := i + 1;
    } else {
      result := false;
      assert 0 <= i;
      assert i < a.Length;
      assert a[0] == v;
      assert a[i] != a[0];
      return;
    }
  }
  result := true;
  assert i == a.Length;
  assert forall t :: 0 <= t < a.Length ==> a[t] == v;
  AllEqualToImpliesPairwise(a, v);
}
// </vc-code>
