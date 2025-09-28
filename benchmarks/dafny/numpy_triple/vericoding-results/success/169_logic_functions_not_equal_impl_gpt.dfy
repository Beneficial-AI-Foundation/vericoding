// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): symmetry of inequality without requiring compiled equality */
lemma NotEqualSymmetric<T>(a: T, b: T)
  ensures (a != b) == (b != a)
{
  assert (a != b) == (b != a);
}

/* helper modified by LLM (iteration 5): every boolean is either true or false */
lemma BoolIsTrueOrFalse(b: bool)
  ensures b == true || b == false
{
  if b {
    assert b == true;
  } else {
    assert b == false;
  }
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
  /* code modified by LLM (iteration 5): build result via array, avoid warnings by using forall statements with ensures */
  var n := |x1|;
  var a := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a.Length == n
    invariant forall j :: 0 <= j < i ==> a[j] == (x1[j] != x2[j])
  {
    a[i] := x1[i] != x2[i];
    i := i + 1;
  }
  result := a[..];
  assert |result| == n;

  // Element-wise inequality relation
  forall j | 0 <= j && j < n
    ensures result[j] == (x1[j] != x2[j])
  {
    assert result[j] == a[..][j];
    assert a[..][j] == a[j];
    assert a[j] == (x1[j] != x2[j]);
  }

  // Irreflexivity when sequences are equal
  if x1 == x2 {
    forall j | 0 <= j && j < n
      ensures result[j] == false
    {
      assert x1[j] == x2[j];
      assert (x1[j] != x2[j]) == false;
      assert result[j] == (x1[j] != x2[j]);
    }
  }

  // Symmetry and boolean result property
  forall k | 0 <= k && k < n
    ensures result[k] == (x2[k] != x1[k])
    ensures result[k] == true || result[k] == false
  {
    assert result[k] == (x1[k] != x2[k]);
    NotEqualSymmetric(x1[k], x2[k]);
    BoolIsTrueOrFalse(result[k]);
  }
}
// </vc-code>
