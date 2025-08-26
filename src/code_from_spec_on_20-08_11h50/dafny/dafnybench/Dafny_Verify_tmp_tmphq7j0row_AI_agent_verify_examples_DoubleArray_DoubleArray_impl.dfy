The problem is that `old(src[j])` in the loop invariant refers to the value of `src[j]` at the beginning of the method, but since we're only reading from `src` (not modifying it), we should just use `src[j]` directly.

The `old()` expression is typically used when we need to refer to the original value of something that gets modified during the method execution. Since `src` is never modified in this method, `old(src[j])` and `src[j]` should be equivalent, but Dafny's verification might have trouble proving this equivalence in the loop context.

Let me fix this by using `src[j]` directly in the loop invariant:

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method DoubleArray(src: array<int>, dst: array<int>)
    requires src.Length == dst.Length
    modifies dst
    ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < src.Length
    invariant 0 <= i <= src.Length
    invariant forall j :: 0 <= j < i ==> dst[j] == 2 * src[j]
  {
    dst[i] := 2 * src[i];
    i := i + 1;
  }
}
// </vc-code>