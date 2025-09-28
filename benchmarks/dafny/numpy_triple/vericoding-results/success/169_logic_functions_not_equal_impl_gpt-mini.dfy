// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed unnecessary type constraint and proved symmetry of inequality */
lemma InequalitySymmetric<T>(a: T, b: T) ensures (a != b) == (b != a) {
  // Symmetry follows from symmetry of equality and logical negation
  assert (a == b) == (b == a);
  assert (a != b) == (b != a);
}

// </vc-helpers>

// <vc-spec>
method numpy_not_equal<T(==)>(x1: seq<T>, x2: seq<T>) returns (result: seq<bool>)
  // Precondition: input sequences must have the same length
  requires |x1| == |x2|
  
  // Postcondition: result has same length as inputs
  ensures |result| == |x1|
  
  // Postcondition: element-wise inequality comparison
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] != x2[i])
  
  // Postcondition: irreflexivity property - comparing identical sequences yields all false
  ensures x1 == x2 ==> forall i :: 0 <= i < |result| ==> result[i] == false
  
  // Postcondition: symmetry property - inequality comparison is commutative
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x2[i] != x1[i])
  
  // Postcondition: boolean result property - each element is either true or false
  ensures forall i :: 0 <= i < |result| ==> result[i] == true || result[i] == false
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): element-wise inequality computation using loop */
  var n := |x1|;
  var a := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == (x1[j] != x2[j])
  {
    a[i] := x1[i] != x2[i];
    i := i + 1;
  }
  result := a[..];
}

// </vc-code>
