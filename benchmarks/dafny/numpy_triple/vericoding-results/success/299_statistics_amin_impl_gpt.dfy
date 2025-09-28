// <vc-preamble>
// Floating point datatype that supports NaN for proper numpy semantics
datatype Float = NaN | Value(val: real)

// Method that returns the minimum element from a non-empty sequence of floating point numbers
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): predicates for NaN detection and value-only sequences */
predicate HasNaN(a: seq<Float>) {
  exists i :: 0 <= i < |a| && a[i] == NaN
}

predicate AllValues(a: seq<Float>) {
  forall i :: 0 <= i < |a| ==> a[i] != NaN
}

/* helper modified by LLM (iteration 2): lemma to derive AllValues from absence of NaN */
lemma NoNaNImpliesAllValues(a: seq<Float>)
  ensures (!HasNaN(a)) ==> AllValues(a)
{
  if !HasNaN(a) {
    assert AllValues(a) by {
      forall i | 0 <= i < |a|
        ensures a[i] != NaN
      {
        if a[i] == NaN {
          assert exists j :: 0 <= j < |a| && a[j] == NaN;
          assert HasNaN(a);
          assert false;
        }
      }
    }
  }
}

/* helper modified by LLM (iteration 2): corrected ensures to reference function name instead of 'result' */
function argMinIndex(a: seq<Float>): nat
  requires |a| > 0
  requires AllValues(a)
  ensures argMinIndex(a) < |a|
  ensures forall i :: 0 <= i < |a| ==> a[argMinIndex(a)].val <= a[i].val
  decreases |a|
{
  if |a| == 1 then
    0
  else if a[argMinIndex(a[..(|a|-1)])].val <= a[|a|-1].val then
    argMinIndex(a[..(|a|-1)])
  else
    |a|-1
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
{
  /* code modified by LLM (iteration 2): propagate NaN; otherwise use argMinIndex to select minimal value */
  if HasNaN(a) {
    result := NaN;
  } else {
    NoNaNImpliesAllValues(a);
    assert AllValues(a);
    var k := argMinIndex(a);
    result := a[k];
  }
}
// </vc-code>
