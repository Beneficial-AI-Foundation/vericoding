// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): allow nullable array in lemma to avoid warning */
lemma ArrayNonNullLengthNonNegative(a: array?<int>)
  requires a != null
  ensures a.Length >= 0
{
  // Length is non-negative for any non-null array
  assert a.Length >= 0;
}

// </vc-helpers>

// <vc-spec>
method Max(a: array<int>) returns (result: int)
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && result == a[i]
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): standard linear scan for maximum with invariants */
  var i := 1;
  var bestIndex := 0;
  var best := a[0];
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= bestIndex < a.Length
    invariant best == a[bestIndex]
    invariant forall j :: 0 <= j < i ==> a[j] <= best
    decreases a.Length - i
  {
    if a[i] > best {
      best := a[i];
      bestIndex := i;
    }
    i := i + 1;
  }
  result := best;
}
// </vc-code>
