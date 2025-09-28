// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma establishing properties of concatenation arr[..index] + arr[index+1..] */
lemma Delete_Concat_Properties(arr: seq<real>, index: nat)
  requires |arr| > 0
  requires index < |arr|
  ensures |arr[..index] + arr[index+1..]| == |arr| - 1
  ensures forall i :: 0 <= i < index ==> (arr[..index] + arr[index+1..])[i] == arr[i]
  ensures forall i :: index <= i < |arr[..index] + arr[index+1..]| ==> (arr[..index] + arr[index+1..])[i] == arr[i+1]
  ensures forall i :: 0 <= i < |arr| && i != index ==> exists j :: 0 <= j < |arr[..index] + arr[index+1..]| && (arr[..index] + arr[index+1..])[j] == arr[i]
{
  // length facts
  assert |arr[..index]| == index;
  assert |arr[index+1..]| == |arr| - (index + 1);
  assert |arr[..index] + arr[index+1..]| == index + (|arr| - (index + 1));
  assert |arr[..index] + arr[index+1..]| == |arr| - 1;

  // elements before index come from the left slice
  assert forall i | 0 <= i < index {
    assert (arr[..index] + arr[index+1..])[i] == arr[..index][i];
    assert arr[..index][i] == arr[i];
  };

  // elements at and after index in the concatenation come from the right slice shifted
  assert forall i | index <= i < |arr[..index] + arr[index+1..]| {
    assert (arr[..index] + arr[index+1..])[i] == arr[index+1..][i - index];
    assert arr[index+1..][i - index] == arr[i + 1];
  };

  // every element of arr except arr[index] appears in the concatenation
  assert forall i | 0 <= i < |arr| {
    if i < index {
      var j := i;
      assert 0 <= j < |arr[..index] + arr[index+1..]|;
      assert (arr[..index] + arr[index+1..])[j] == arr[i];
    } else if i > index {
      var j := i - 1;
      assert 0 <= j < |arr[..index] + arr[index+1..]|;
      assert (arr[..index] + arr[index+1..])[j] == arr[i];
    } else {
      // i == index: skipped
    }
  };
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
  /* code modified by LLM (iteration 5): construct result by concatenation and call lemma to prove postconditions */
  result := arr[..index] + arr[index+1..];
  assert result == arr[..index] + arr[index+1..];
  Delete_Concat_Properties(arr, index);
  assert |result| == |arr| - 1;
  assert forall i :: 0 <= i < index ==> result[i] == arr[i];
  assert forall i :: index <= i < |result| ==> result[i] == arr[i + 1];
  assert forall i :: 0 <= i < |arr| && i != index ==> exists j :: 0 <= j < |result| && result[j] == arr[i];
}

// </vc-code>
