// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed redundant non-null requirement to avoid warning */
predicate AllGreater(n: int, a: array<int>)
  reads a
{
  forall i :: 0 <= i < a.Length ==> n > a[i]
}
// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result == (forall i :: 0 <= i < a.Length ==> n > a[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute result directly using quantified condition matching ensures */
  result := (forall i :: 0 <= i < a.Length ==> n > a[i]);
}
// </vc-code>
