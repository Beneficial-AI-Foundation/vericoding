// <vc-preamble>
/*
 * Dafny specification for numpy.putmask functionality.
 * Changes elements of an array based on conditional and input values,
 * with cyclic repetition of values when the values array is smaller.
 */
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method putmask(a: seq<real>, mask: seq<bool>, values: seq<real>) returns (result: seq<real>)
    // Preconditions: arrays must have same length, values must be non-empty
    requires |a| == |mask|
    requires |values| > 0
    
    // Postconditions: specify the exact behavior of putmask
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> 
        (mask[i] ==> result[i] == values[i % |values|])
    ensures forall i :: 0 <= i < |result| ==> 
        (!mask[i] ==> result[i] == a[i])
    ensures forall i :: 0 <= i < |result| ==> 
        (mask[i] ==> exists j :: 0 <= j < |values| && result[i] == values[j])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Replaced seq comprehension with a while loop to resolve a compile-time index check failure. */
  var i := 0;
  result := [];
  while i < |a|
    invariant |result| == i
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> (mask[k] ==> result[k] == values[k % |values|])
    invariant forall k :: 0 <= k < i ==> (!mask[k] ==> result[k] == a[k])
  {
    if mask[i] {
      result := result + [values[i % |values|]];
    } else {
      result := result + [a[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
