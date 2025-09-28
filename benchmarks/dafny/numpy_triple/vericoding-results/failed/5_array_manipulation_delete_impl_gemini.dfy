// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added assertions to break down proof step */
lemma PreservesElementsAfterDelete<T>(arr: seq<T>, index: nat, res: seq<T>)
  requires index < |arr|
  requires res == arr[..index] + arr[index+1..]
  ensures forall i :: 0 <= i < |arr| && i != index ==>
    exists j :: 0 <= j < |res| && res[j] == arr[i]
{
  forall i | 0 <= i < |arr| && i != index
    ensures exists j :: 0 <= j < |res| && res[j] == arr[i]
  {
    if i < index {
      var j := i;
      assert res[j] == arr[i];
    } else { // i > index
      var j := i - 1;
      assert |arr[..index]| == index;
      assert res[j] == arr[index+1..][j - index];
      assert arr[index+1..][j-index] == arr[index+1 + (j-index)];
      assert index+1+(j-index) == i;
      assert res[j] == arr[i];
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
  /* code modified by LLM (iteration 5): logic is sound, relying on fixed helper lemma */
  result := arr[..index] + arr[index+1..];
  PreservesElementsAfterDelete(arr, index, result);
}
// </vc-code>
