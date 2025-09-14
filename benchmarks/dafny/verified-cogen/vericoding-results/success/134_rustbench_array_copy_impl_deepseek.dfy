// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function arrayLength<T>(a: array<T>): nat { a.Length }

predicate arraysEqual(a: array<int>, b: array<int>)
  reads a, b
{
  a.Length == b.Length &&
  (forall i: int :: 0 <= i < a.Length ==> a[i] == b[i])
}

lemma ArrayCopyLemma(a: array<int>, result: array<int>)
  requires result.Length == a.Length
  requires forall i :: 0 <= i < a.Length ==> result[i] == a[i]
  ensures arraysEqual(a, result)
{
}
// </vc-helpers>

// <vc-spec>
method ArrayCopy(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed array copy implementation */
{
  result := new int[a.Length];
  var j := 0;
  while j < a.Length
    invariant 0 <= j <= a.Length
    invariant forall i :: 0 <= i < j ==> result[i] == a[i]
  {
    result[j] := a[j];
    j := j + 1;
  }
}
// </vc-code>
