// <vc-preamble>
// Array representation using sequences of real numbers
type Array = seq<real>
// </vc-preamble>

// <vc-helpers>

function array_length(a: Array): nat
{
  |a|
}

function array_start(a: Array): int
{
  0
}

function array_end(a: Array): int
{
  if |a| == 0 then 0 else |a| - 1
}

predicate arrays_may_overlap(a: Array, b: Array)
{
  array_start(a) <= array_end(b) && array_start(b) <= array_end(a)
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
  result := arrays_may_overlap(a, b);
}
// </vc-code>
