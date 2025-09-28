// <vc-preamble>
// Method that computes the logical AND of two boolean sequences element-wise
// Each element of the result is the logical AND of the corresponding elements from the input sequences
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): proves commutativity of boolean AND */
lemma BoolAndCommutes(a: bool, b: bool)
  ensures (a && b) == (b && a)
{
  if a {
    if b {
      assert (a && b) == true;
      assert (b && a) == true;
      assert (a && b) == (b && a);
    } else {
      assert (a && b) == false;
      assert (b && a) == false;
      assert (a && b) == (b && a);
    }
  } else {
    if b {
      assert (a && b) == false;
      assert (b && a) == false;
      assert (a && b) == (b && a);
    } else {
      assert (a && b) == false;
      assert (b && a) == false;
      assert (a && b) == (b && a);
    }
  }
}

/* helper modified by LLM (iteration 4): true is left-identity for boolean AND */
lemma BoolAndLeftIdentity(a: bool)
  ensures (true && a) == a
{
  if a {
    assert (true && a) == true;
    assert a == true;
    assert (true && a) == a;
  } else {
    assert (true && a) == false;
    assert a == false;
    assert (true && a) == a;
  }
}

// </vc-helpers>

// <vc-spec>
method LogicalAnd(x1: seq<bool>, x2: seq<bool>) returns (result: seq<bool>)
    // Precondition: input sequences must have the same length
    requires |x1| == |x2|
    
    // Postcondition: result has same length as inputs
    ensures |result| == |x1|
    
    // Postcondition: each element is the logical AND of corresponding input elements  
    ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] && x2[i])
    
    // Additional properties that follow from the specification:
    // Commutativity: LogicalAnd(x1, x2) equivalent to LogicalAnd(x2, x1)
    // Identity: LogicalAnd(x, all_true_seq) equivalent to x
    // Zero: LogicalAnd(x, all_false_seq) equivalent to all_false_seq  
    // Idempotent: LogicalAnd(x, x) equivalent to x
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): element-wise logical AND implemented with loop */
  var n := |x1|;
  var a := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == (x1[j] && x2[j])
  {
    a[i] := x1[i] && x2[i];
    i := i + 1;
  }
  result := a[..];
}

// </vc-code>
