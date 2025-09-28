// <vc-preamble>
// Method that performs element-wise equality comparison
// </vc-preamble>

// <vc-helpers>
function CreateBoolSequence(length: int): seq<bool>
  requires length >= 0
  ensures |CreateBoolSequence(length)| == length
{
  if length == 0 then [] else [false] + CreateBoolSequence(length - 1)
}
// </vc-helpers>

// <vc-spec>
method NumpyEqual<T(==)>(x1: seq<T>, x2: seq<T>) returns (result: seq<bool>)
  // Precondition: input sequences must have the same length
  requires |x1| == |x2|
  
  // Postcondition: result has same length as inputs
  ensures |result| == |x1|
  
  // Postcondition: element-wise comparison property
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] == x2[i])
  
  // Postcondition: reflexivity - if vectors are equal, all results are true
  ensures x1 == x2 ==> forall i :: 0 <= i < |result| ==> result[i] == true
  
  // Postcondition: symmetry - equality comparison is commutative  
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x2[i] == x1[i])
  
  // Postcondition: boolean result property - each element is either true or false
  ensures forall i :: 0 <= i < |result| ==> result[i] == true || result[i] == false
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := CreateBoolSequence(|x1|);
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == |x1|
    invariant forall j :: 0 <= j < i ==> result[j] == (x1[j] == x2[j])
  {
    result := result[i := (x1[i] == x2[i])];
    i := i + 1;
  }
}
// </vc-code>
