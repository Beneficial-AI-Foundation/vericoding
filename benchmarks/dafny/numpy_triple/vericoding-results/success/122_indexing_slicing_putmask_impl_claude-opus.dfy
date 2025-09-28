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
  result := [];
  var valueIndex := 0;
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant 0 <= valueIndex <= |values|
    invariant forall k :: 0 <= k < i ==> (mask[k] ==> result[k] == values[k % |values|])
    invariant forall k :: 0 <= k < i ==> (!mask[k] ==> result[k] == a[k])
  {
    if mask[i] {
      result := result + [values[i % |values|]];
    } else {
      result := result + [a[i]];
    }
  }
}
// </vc-code>
