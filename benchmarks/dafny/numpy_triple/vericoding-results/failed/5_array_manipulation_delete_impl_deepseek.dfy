// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed helper function with proper syntax */
function ConditionalIndex(k: nat, index: nat): nat
  requires k >= 0
{
  if k < index then k else k - 1
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
  /* code modified by LLM (iteration 5): Fixed while loop with proper syntax */
  result := [];
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |result| == i - (if i > index then 1 else 0)
    invariant forall k :: 0 <= k < i && k != index ==> result[ConditionalIndex(k, index)] == arr[k]
  {
    if i != index {
      result := result + [arr[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
