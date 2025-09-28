// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): commutativity of or */
lemma OrCommutative(a: bool, b: bool)
  ensures a || b == b || a
{
  if a {
    assert a || b == true;
    assert b || a == true;
  } else {
    assert a || b == b;
    assert b || a == b;
  }
}

/* helper modified by LLM (iteration 2): identity with false */
lemma OrIdentityFalse(a: bool)
  ensures a || false == a
{
  if a {
    assert a || false == true;
  } else {
    assert a || false == false;
  }
}

/* helper modified by LLM (iteration 2): absorption with true */
lemma OrAbsorptionTrue(a: bool)
  ensures a || true == true
{
  if a {
    assert a || true == true;
  } else {
    assert a || true == true;
  }
}

/* helper modified by LLM (iteration 2): idempotent property */
lemma OrIdempotent(a: bool)
  ensures a || a == a
{
  if a {
    assert a || a == true;
  } else {
    assert a || a == false;
  }
}

/* helper modified by LLM (iteration 2): true if either operand true */
lemma OrTrueIfEither(a: bool, b: bool)
  ensures (a == true || b == true) ==> (a || b) == true
{
  if a {
    assert a || b == true;
  } else if b {
    assert a || b == true;
  } else {
    // antecedent false, vacuously holds
  }
}

/* helper modified by LLM (iteration 2): false if both operands false */
lemma OrFalseIfBoth(a: bool, b: bool)
  ensures (a == false && b == false) ==> (a || b) == false
{
  if a {
    // antecedent false, nothing to prove
  } else {
    if b {
      // antecedent false
    } else {
      assert a || b == false;
    }
  }
}

// </vc-helpers>

// <vc-spec>
method logical_or(x1: seq<bool>, x2: seq<bool>) returns (result: seq<bool>)
  // Input vectors must have the same length
  requires |x1| == |x2|
  
  // Output vector has the same length as input vectors
  ensures |result| == |x1|
  
  // Core specification: each element is logical OR of corresponding input elements
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] || x2[i])
  
  // Commutativity property: a ∨ b = b ∨ a
  ensures forall i :: 0 <= i < |result| ==> (x1[i] || x2[i]) == (x2[i] || x1[i])
  
  // Identity with false: a ∨ false = a
  ensures forall i :: 0 <= i < |x1| ==> (x1[i] || false) == x1[i]
  
  // Absorption with true: a ∨ true = true
  ensures forall i :: 0 <= i < |x1| ==> (x1[i] || true) == true
  
  // Idempotent property: a ∨ a = a
  ensures forall i :: 0 <= i < |x1| ==> (x1[i] || x1[i]) == x1[i]
  
  // Result is true if either operand is true
  ensures forall i :: 0 <= i < |result| ==> 
    (x1[i] == true || x2[i] == true) ==> result[i] == true
  
  // Result is false only when both operands are false
  ensures forall i :: 0 <= i < |result| ==> 
    (x1[i] == false && x2[i] == false) ==> result[i] == false
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented element-wise OR using array */
  var n := |x1|;
  var arr := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> arr[j] == (x1[j] || x2[j])
  {
    arr[i] := x1[i] || x2[i];
    i := i + 1;
  }
  result := arr[..];
}

// </vc-code>
