// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): using a forall statement for a more direct implementation */
{
  result := forall i :: 0 <= i < a.Length ==> a[i] == n;
}
// </vc-code>
