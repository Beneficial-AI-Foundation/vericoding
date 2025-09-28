// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added reads clause to allow reading array elements */
predicate IsPrefix(a: array<int>, key: int, k: int)
  requires 0 <= k <= a.Length
  reads a
{
  forall i :: 0 <= i < k ==> a[i] != key
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
/* code modified by LLM (iteration 2): Fixed implementation to correctly find the first occurrence of key */
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant IsPrefix(a, key, i)
  {
    if a[i] == key {
      return i;
    }
    i := i + 1;
  }
  return -1;
}
// </vc-code>
