// <vc-preamble>
predicate IsOdd(x: int)
{
    x % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed helper as it was inlined */
// </vc-helpers>

// <vc-spec>
method FindFirstOdd(a: array<int>) returns (found: bool, index: int)
    requires a != null
    ensures !found ==> forall i :: 0 <= i < a.Length ==> !IsOdd(a[i])
    ensures found ==> 0 <= index < a.Length && IsOdd(a[index]) && forall i :: 0 <= i < index ==> !IsOdd(a[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): inlined helper predicate into loop invariant */
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> !IsOdd(a[k])
  {
    if IsOdd(a[i]) {
      found := true;
      index := i;
      return;
    }
    i := i + 1;
  }
  found := false;
  index := a.Length;
}
// </vc-code>
