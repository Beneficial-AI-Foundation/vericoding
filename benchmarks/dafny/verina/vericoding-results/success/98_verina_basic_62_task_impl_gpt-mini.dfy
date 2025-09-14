// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause to allow array element access */
predicate NoOccurrence(a: array<int>, key: int) reads a { forall i :: 0 <= i < a.Length ==> a[i] != key }
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
  /* code modified by LLM (iteration 2): linear search that returns first occurrence index or -1 */
  var i := 0;
  result := -1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != key
    decreases a.Length - i
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
