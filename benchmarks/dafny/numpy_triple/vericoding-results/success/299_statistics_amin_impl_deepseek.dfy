// <vc-preamble>
// Floating point datatype that supports NaN for proper numpy semantics
datatype Float = NaN | Value(val: real)

// Method that returns the minimum element from a non-empty sequence of floating point numbers
// </vc-preamble>

// <vc-helpers>

  predicate isNaN(f: Float) { f == NaN }
  predicate isValue(f: Float) { f.Value? }
  function realValue(f: Float): real
    requires f.Value?
  {
    f.val
  }
  lemma valueComparison(f1: Float, f2: Float)
    requires f1.Value? && f2.Value?
    ensures f1.val <= f2.val || f2.val <= f1.val
  {
  }
  /* helper modified by LLM (iteration 3): Added lemma to prove minimum property */
  lemma minProperty(a: seq<Float>, minVal: Float, index: int)
    requires 0 <= index <= |a|
    requires minVal.Value?
    requires (forall i :: 0 <= i < index ==> a[i].Value? && minVal.val <= a[i].val)
    requires (exists i :: 0 <= i < index && a[i] == minVal)
    ensures (forall i :: 0 <= i < index ==> minVal.val <= a[i].val)
  {
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
  /* code modified by LLM (iteration 3): Fixed NaN propagation postcondition */
  var index := 0;
  var foundNaN := false;
  var currentMin := a[0];
  
  while index < |a|
    invariant 0 <= index <= |a|
    invariant foundNaN ==> (exists i :: 0 <= i < index && a[i] == NaN)
    invariant !foundNaN ==> (forall i :: 0 <= i < index ==> a[i] != NaN)
    invariant !foundNaN && index > 0 ==> currentMin.Value?
    invariant !foundNaN && index > 0 ==> (exists i :: 0 <= i < index && a[i] == currentMin)
    invariant !foundNaN && index > 0 ==> (forall i :: 0 <= i < index ==> a[i].Value? && currentMin.val <= a[i].val)
  {
    if a[index] == NaN {
      foundNaN := true;
      currentMin := NaN;
    } else if !foundNaN {
      if index == 0 {
        currentMin := a[index];
      } else if a[index].Value? && currentMin.Value? {
        if a[index].val < currentMin.val {
          currentMin := a[index];
        }
      }
    }
    index := index + 1;
  }
  
  if foundNaN {
    result := NaN;
  } else {
    result := currentMin;
  }
}
// </vc-code>
