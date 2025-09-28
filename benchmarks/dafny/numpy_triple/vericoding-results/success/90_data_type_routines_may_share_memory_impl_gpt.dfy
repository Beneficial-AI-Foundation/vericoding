// <vc-preamble>
// Array representation using sequences of real numbers
type Array = seq<real>
// </vc-preamble>

// <vc-helpers>
function minLen(a: Array, b: Array): nat
{
  if |a| <= |b| then |a| else |b|
}

predicate NonEmpty(a: Array)
{
  |a| > 0
}

function mayShareHeuristic(a: Array, b: Array): bool
{
  if |a| > 0 && |b| > 0 then a[0] == b[0] else false
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
  if |a| == 0 || |b| == 0 {
    result := false;
  } else {
    result := a[0] == b[0];
  }
}
// </vc-code>
