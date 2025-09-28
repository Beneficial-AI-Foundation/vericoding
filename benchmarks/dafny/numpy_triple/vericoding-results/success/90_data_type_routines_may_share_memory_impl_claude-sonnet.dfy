// <vc-preamble>
// Array representation using sequences of real numbers
type Array = seq<real>
// </vc-preamble>

// <vc-helpers>
function arraysEqual(a: Array, b: Array): bool
{
  a == b
}

function arraysOverlap(a: Array, b: Array): bool
{
  |a| > 0 && |b| > 0 && exists i, j :: 0 <= i < |a| && 0 <= j < |b| && a[i] == b[j]
}
// </vc-helpers>

// <vc-spec>
method may_share_memory(a: Array, b: Array) returns (result: bool)
  // No preconditions needed - function accepts any two arrays
  requires true
  // Conservative property: function provides conservative bounds checking
  // May return true even when arrays don't actually share memory
  // May return false when unsure about memory sharing
  ensures true  // Function is deterministic but result depends on implementation details
// </vc-spec>
// <vc-code>
{
  result := arraysEqual(a, b) || arraysOverlap(a, b);
}
// </vc-code>
