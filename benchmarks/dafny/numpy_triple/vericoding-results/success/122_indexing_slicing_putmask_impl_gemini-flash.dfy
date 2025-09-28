// <vc-preamble>
/*
 * Dafny specification for numpy.putmask functionality.
 * Changes elements of an array based on conditional and input values,
 * with cyclic repetition of values when the values array is smaller.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no changes */
function get_value_cyclic(values: seq<real>, index: int): real
    requires |values| > 0
    requires index >= 0
{
    values[index % |values|]
}
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
/* code modified by LLM (iteration 4): fixing compilation error (missing brace) */
{
  var new_a := new real[|a|];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant new_a.Length == |a|
    invariant forall k :: 0 <= k < i && mask[k] ==> new_a[k] == get_value_cyclic(values, k)
    invariant forall k :: 0 <= k < i && !mask[k] ==> new_a[k] == a[k]
  {
    if i == |a| { break; } // Exit loop when i reaches |a|
    if mask[i] {
      new_a[i] := get_value_cyclic(values, i);
    } else {
      new_a[i] := a[i];
    }
  }
  return new_a[..];
}
// </vc-code>
