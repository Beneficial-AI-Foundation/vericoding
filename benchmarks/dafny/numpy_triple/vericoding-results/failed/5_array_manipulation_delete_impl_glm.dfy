// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): lemma to prove that all elements except the deleted one are preserved */
lemma DeletePreservesElements(arr: seq<real>, index: nat, result: seq<real>)
  requires |result| == |arr| - 1
  requires forall i :: 0 <= i < index ==> result[i] == arr[i]
  requires forall i :: index <= i < |result| ==> result[i] == arr[i + 1]
  ensures forall i :: 0 <= i < |arr| && i != index ==> 
    exists j :: 0 <= j < |result| && result[j] == arr[i]
{
  forall i | 0 <= i < |arr| && i != index
  {
    if i < index {
      assert result[i] == arr[i];
    } else {
      assert i > index;
      assert result[i-1] == arr[i];
    }
  }
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
{
  /* code modified by LLM (iteration 4): using slice concatenation and helper lemma to prove postcondition */
  result := arr[..index] + arr[index+1..];
  DeletePreservesElements(arr, index, result);
}
// </vc-code>
