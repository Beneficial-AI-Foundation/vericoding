// <vc-preamble>
/*
 * Dafny specification for numpy.insert functionality.
 * Insert values along the given axis before the given indices.
 * Creates a new sequence with values inserted at specified positions.
 */
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NumpyInsert<T>(arr: seq<T>, idx: int, value: T) returns (result: seq<T>)
  // Precondition: index must be valid (0 to length of array inclusive)
  requires 0 <= idx <= |arr|
  
  // Postconditions
  ensures |result| == |arr| + 1  // Size: result has exactly one more element
  
  // Preservation: elements before insertion point are preserved at original indices
  ensures forall i :: 0 <= i < idx ==> result[i] == arr[i]
  
  // Insertion: the new value is placed exactly at the specified index
  ensures result[idx] == value
  
  // Shifting: elements at or after insertion point are shifted right by one position
  ensures forall i :: idx < i < |result| ==> result[i] == arr[i-1]
  
  // Sanity check: all original elements are preserved in the result
  ensures forall j :: 0 <= j < |arr| ==> 
    (j < idx ==> result[j] == arr[j]) &&
    (j >= idx ==> result[j+1] == arr[j])
// </vc-spec>
// <vc-code>
{
  result := arr[..idx] + [value] + arr[idx..];
}
// </vc-code>
