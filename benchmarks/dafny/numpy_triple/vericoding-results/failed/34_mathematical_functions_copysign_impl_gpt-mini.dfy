// <vc-preamble>
// Helper function to compute absolute value of a real number
function abs(x: real): real
{
  if x >= 0.0 then x else -x
}

// Helper function to determine sign of a real number (1.0 for non-negative, -1.0 for negative)
function sign(x: real): real
{
  if x >= 0.0 then 1.0 else -1.0
}

/**
 * copysign operation: returns a sequence where each element has the magnitude 
 * of the corresponding element in x1 but the sign of the corresponding element in x2.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma about sign function */
lemma SignLemma(b: real)
  ensures (b >= 0.0 ==> sign(b) == 1.0) && (b < 0.0 ==> sign(b) == -1.0)
{
  if b >= 0.0 {
    assert sign(b) == 1.0;
  } else {
    assert sign(b) == -1.0;
  }
}

/* helper modified by LLM (iteration 5): scalar copy-sign function returning conditional magnitude with sign of b */
function CopySignScalar(a: real, b: real): real
{
  if b >= 0.0 then abs(a) else -abs(a)
}

/* helper modified by LLM (iteration 5): relates CopySignScalar to multiplication by sign(b) */
lemma CopySignScalarSignLemma(a: real, b: real)
  ensures CopySignScalar(a,b) == abs(a) * sign(b)
{
  SignLemma(b);
  if b >= 0.0 {
    assert sign(b) == 1.0;
    assert CopySignScalar(a,b) == abs(a);
    assert abs(a) * sign(b) == abs(a) * 1.0;
    assert CopySignScalar(a,b) == abs(a) * sign(b);
  } else {
    assert sign(b) == -1.0;
    assert CopySignScalar(a,b) == -abs(a);
    assert abs(a) * sign(b) == abs(a) * -1.0;
    assert CopySignScalar(a,b) == abs(a) * sign(b);
  }
}
// </vc-helpers>

// <vc-spec>
method copysign(x1: seq<real>, x2: seq<real>) returns (result: seq<real>)
  // Precondition: input vectors must have the same length
  requires |x1| == |x2|
  
  // Postcondition: result has same length as inputs
  ensures |result| == |x1|
  
  // Postcondition: for each element, the sign copying and magnitude preservation properties hold
  ensures forall i :: 0 <= i < |result| ==>
    // Basic behavior: sign copying with magnitude preservation
    (x2[i] >= 0.0 ==> result[i] == abs(x1[i])) &&
    (x2[i] < 0.0 ==> result[i] == -abs(x1[i]))
  
  // Postcondition: magnitude preservation property
  ensures forall i :: 0 <= i < |result| ==>
    abs(result[i]) == abs(x1[i])
  
  // Postcondition: sign copying property
  ensures forall i :: 0 <= i < |result| ==>
    (x2[i] >= 0.0 ==> result[i] >= 0.0) &&
    (x2[i] < 0.0 ==> result[i] < 0.0)
  
  // Postcondition: mathematical equivalence using sign function
  ensures forall i :: 0 <= i < |result| ==>
    result[i] == abs(x1[i]) * sign(x2[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): build result array using CopySignScalar and prove postconditions */
  var n := |x1|;
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == CopySignScalar(x1[j], x2[j])
    decreases n - i
  {
    var v := CopySignScalar(x1[i], x2[i]);
    a[i] := v;
    i := i + 1;
  }
  result := a[..];

  var k := 0;
  while k < n
    invariant 0 <= k <= n
    decreases n - k
  {
    // Relate the constructed result to abs and sign, and prove required properties
    assert result[k] == CopySignScalar(x1[k], x2[k]);
    CopySignScalarSignLemma(x1[k], x2[k]);
    assert result[k] == abs(x1[k]) * sign(x2[k]);
    // Now prove the conditional equalities and magnitude/sign properties
    if x2[k] >= 0.0 {
      SignLemma(x2[k]);
      assert sign(x2[k]) == 1.0;
      assert result[k] == abs(x1[k]);
      assert result[k] >= 0.0;
      assert abs(result[k]) == abs(x1[k]);
    } else {
      SignLemma(x2[k]);
      assert sign(x2[k]) == -1.0;
      assert result[k] == -abs(x1[k]);
      assert result[k] < 0.0;
      assert abs(result[k]) == abs(x1[k]);
    }
    k := k + 1;
  }
}

// </vc-code>
