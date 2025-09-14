// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed for this implementation. */
// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
    ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Reverted to a while-loop implementation as the forall expression might be causing a toolchain issue. */
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> n > a[k]
  {
    if n <= a[i] {
        result := false;
        return;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>
