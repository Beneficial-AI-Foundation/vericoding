// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed redundant null check precondition to eliminate warning */
function Contains(a: array<int>, x: int): bool
  reads a
{
  x in a[..]
}
// </vc-helpers>

// <vc-spec>
method AnyValueExists(arr1: array<int>, arr2: array<int>) returns (result: bool)
    ensures result == exists k :: 0 <= k < arr1.Length && k in arr2[..]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): assign result to the existential specified in ensures */
  result := exists k :: 0 <= k < arr1.Length && k in arr2[..];
}
// </vc-code>
