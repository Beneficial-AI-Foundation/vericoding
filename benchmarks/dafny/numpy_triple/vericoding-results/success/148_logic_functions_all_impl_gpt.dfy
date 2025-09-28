// <vc-preamble>
// Test whether all elements in a sequence are non-zero
// </vc-preamble>

// <vc-helpers>
function NonZeroAll(a: seq<real>): bool
{
  forall i :: 0 <= i < |a| ==> a[i] != 0.0
}
// </vc-helpers>

// <vc-spec>
method All(a: seq<real>) returns (result: bool)
    // The result is true if and only if all elements are non-zero
    ensures result == (forall i :: 0 <= i < |a| ==> a[i] != 0.0)
// </vc-spec>
// <vc-code>
{
  result := NonZeroAll(a);
}
// </vc-code>
