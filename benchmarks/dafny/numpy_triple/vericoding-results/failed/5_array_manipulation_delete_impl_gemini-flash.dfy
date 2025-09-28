// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes required */
function Slice(s: seq<real>, start: nat, end: nat): seq<real>
  requires 0 <= start <= end <= |s|
{
  s[start .. end]
}
// </vc-helpers>

// <vc-spec>
method Delete(arr: seq<real>, index: nat) returns (result: seq<real>)
  // Preconditions: array must be non-empty and index must be valid
  requires |arr| > 0
  requires index < |arr|
  
  // Postcondition: result has exactly one fewer element
  ensures |result| == |arr| - 1
  
  // Postcondition: elements before the deleted index maintain their positions  
  ensures forall i :: 0 <= i < index ==> result[i] == arr[i]
  
  // Postcondition: elements after the deleted index are shifted left by one
  ensures forall i :: index <= i < |result| ==> result[i] == arr[i + 1]
  
  // Postcondition: every element except the deleted one appears in the result
  ensures forall i :: 0 <= i < |arr| && i != index ==> 
    exists j :: 0 <= j < |result| && result[j] == arr[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The fixes focus on ensuring the postconditions are rigorously proven. Specifically, the third ensures clause regarding the existence of elements after deletion required a more precise proof block, which was implemented. Assertions for `left_slice` and `right_slice` lengths were added to strengthen the proof for the first ensures clause. */
{
  var left_slice := Slice(arr, 0, index);
  var right_slice := Slice(arr, index + 1, |arr|);
  result := left_slice + right_slice;

  // Proof for ensures clauses
  // ensure |result| == |arr| - 1
  assert |left_slice| == index; // Property of sequence slicing.
  assert |right_slice| == |arr| - (index + 1); // Property of sequence slicing.
  assert |result| == index + (|arr| - (index + 1)) == |arr| - 1;

  // ensure forall i :: 0 <= i < index ==> result[i] == arr[i]
  forall i | 0 <= i < index
    ensures result[i] == arr[i]
  {
    assert result[i] == left_slice[i];
    assert left_slice[i] == arr[i];
  }

  // ensure forall i :: index <= i < |result| ==> result[i] == arr[i + 1]
  forall i | index <= i < |result|
    ensures result[i] == arr[i + 1]
  {
    assert result[i] == right_slice[i - index];
    assert right_slice[i - index] == arr[(i - index) + (index + 1)];
  }

  // ensure forall i :: 0 <= i < |arr| && i != index ==> exists j :: 0 <= j < |result| && result[j] == arr[i]
  forall i | 0 <= i < |arr| && i != index
    ensures exists j :: 0 <= j < |result| && result[j] == arr[i]
  {
    if i < index {
      // The element arr[i] is at result[i]
      assert exists j :: 0 <= j < |result| && result[j] == arr[i] by { var j := i; assert 0 <= j < index; assert result[j] == arr[i]; }
    } else if i > index {
      // The element arr[i] is shifted to result[i - 1]
      assert exists j :: 0 <= j < |result| && result[j] == arr[i] by { var j := i - 1; assert index <= j < |result|; assert result[j] == arr[i]; }
    }
  }
}
// </vc-code>
