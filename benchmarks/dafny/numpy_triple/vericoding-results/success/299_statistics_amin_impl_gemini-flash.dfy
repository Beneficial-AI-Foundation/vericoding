// <vc-preamble>
// Floating point datatype that supports NaN for proper numpy semantics
datatype Float = NaN | Value(val: real)

// Method that returns the minimum element from a non-empty sequence of floating point numbers
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): consolidated helper functions, removed redundant predicates */
function min_float(f1: Float, f2: Float): Float
  requires f1.Value? && f2.Value?
{
  if f1.val < f2.val then f1 else f2
}
// </vc-helpers>

// <vc-spec>
method amin(a: seq<Float>) returns (result: Float)
  // Precondition: array must be non-empty since minimum is undefined for empty sets
  requires |a| > 0
  // Postcondition 1: if any element is NaN, result is NaN (NaN propagation)
  ensures (exists i :: 0 <= i < |a| && a[i] == NaN) ==> result == NaN
  // Postcondition 2: if no NaN present, result must be an actual element from the input array
  ensures (forall i :: 0 <= i < |a| ==> a[i] != NaN) ==> (exists i :: 0 <= i < |a| && a[i] == result)
  // Postcondition 3: if no NaN present, result must be less than or equal to all elements
  ensures (forall i :: 0 <= i < |a| ==> a[i] != NaN) ==> (forall i :: 0 <= i < |a| ==> a[i].Value? ==> result.Value? && result.val <= a[i].val)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): removed 'skip;' statement and fixed compilation errors */
{
  var result_f: Float := a[0];
  var i: int := 1;

  while i < |a|
    invariant 1 <= i <= |a|
    invariant (exists k :: 0 <= k < i && a[k].NaN?) ==> result_f.NaN?
    invariant (forall k :: 0 <= k < i ==> a[k].Value?) ==> result_f.Value?
    invariant (forall k :: 0 <= k < i ==> a[k].Value?) ==> (exists k :: 0 <= k < i && result_f == a[k])
    invariant (forall k :: 0 <= k < i ==> a[k].Value?) ==> (forall k :: 0 <= k < i ==> result_f.val <= a[k].val)
  {
    if result_f.NaN? {
      // Once result_f is NaN, it stays NaN
    } else if a[i].NaN? {
      result_f := NaN;
    } else if a[i].val < result_f.val {
      result_f := a[i];
    }
    i := i + 1;
  }
  result := result_f;
}
// </vc-code>
