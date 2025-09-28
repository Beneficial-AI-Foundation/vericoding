// <vc-preamble>
// Method that performs element-wise equality comparison
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemma that equality of sequences implies element-wise equality */
lemma SeqEqImpliesElemEq<T>(x: seq<T>, y: seq<T>)
  requires |x| == |y|
  requires x == y
  ensures forall i :: 0 <= i < |x| ==> x[i] == y[i]
{
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
  /* code modified by LLM (iteration 2): implement element-wise equality with proper invariants */
  var res: seq<bool> := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == (x1[j] == x2[j])
  {
    var b := x1[i] == x2[i];
    res := res + [b];
    i := i + 1;
  }
  result := res;
}

// </vc-code>
