// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result == (forall i :: 0 <= i < a.Length ==> n > a[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): refined loop invariant by removing redundant condition for better verification */
  var i := 0;
  result := true;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> n > a[k]
  {
    if a[i] >= n {
      result := false;
      break;
   }
    i := i + 1;
  }
}
// </vc-code>
