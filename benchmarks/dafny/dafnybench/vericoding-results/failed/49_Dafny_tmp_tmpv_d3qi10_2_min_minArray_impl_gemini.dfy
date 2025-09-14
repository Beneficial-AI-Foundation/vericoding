// <vc-preamble>
function min(a: int, b: int): int
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{
    if a < b then a else b
}

ghost function minFunction(a: int, b: int): int
    ensures minFunction(a, b) <= a && minFunction(a, b) <= b
    ensures minFunction(a, b) == a || minFunction(a, b) == b
{
    if a < b then a else b
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method minArray(a: array<int>) returns (m: int)
    requires a!= null  && a.Length > 0 
    ensures forall k | 0 <= k < a.Length :: m <= a[k]
    ensures exists k | 0 <= k < a.Length :: m == a[k]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Replaced the for-loop with an equivalent while-loop. The previous submission was logically correct but failed due to a compiler warning in the non-editable specification section. This change is an attempt to work around the toolchain issue. */
  m := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> m <= a[k]
    invariant exists k :: 0 <= k < i && m == a[k]
  {
    if a[i] < m {
      m := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>
