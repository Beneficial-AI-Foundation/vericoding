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
/* helper modified by LLM (iteration 5): strengthen lemma for strict negativity */
lemma AbsSignProperties(x: real, y: real)
  ensures abs(abs(x) * sign(y)) == abs(x)
  ensures (y >= 0.0 ==> abs(x) * sign(y) >= 0.0)
  ensures (y < 0.0 ==> abs(x) * sign(y) <= 0.0)
  ensures (y >= 0.0 ==> abs(x) * sign(y) == abs(x))
  ensures (y < 0.0 ==> abs(x) * sign(y) == -abs(x))
  ensures (y < 0.0 ==> abs(x) * sign(y) < 0.0)
  ensures (y < 0.0 ==> -abs(x) < 0.0)
{
  if y >= 0.0 {
    assert sign(y) == 1.0;
    assert abs(x) * sign(y) == abs(x);
  } else {
    assert sign(y) == -1.0;
    assert abs(x) * sign(y) == -abs(x);
    assert abs(x) >= 0.0;
    assert -abs(x) <= 0.0;
    assert -abs(x) < 0.0;
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
  /* code modified by LLM (iteration 5): fix strict negativity requirement */
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      (x2[j] >= 0.0 ==> result[j] == abs(x1[j])) &&
      (x2[j] < 0.0 ==> result[j] == -abs(x1[j]))
    invariant forall j :: 0 <= j < i ==>
      abs(result[j]) == abs(x1[j])
    invariant forall j :: 0 <= j < i ==>
      (x2[j] >= 0.0 ==> result[j] >= 0.0) &&
      (x2[j] < 0.0 ==> result[j] < 0.0)
    invariant forall j :: 0 <= j < i ==>
      result[j] == abs(x1[j]) * sign(x2[j])
  {
    var value: real;
    if x2[i] >= 0.0 {
      value := abs(x1[i]);
    } else {
      value := -abs(x1[i]);
    }
    AbsSignProperties(x1[i], x2[i]);
    if x2[i] < 0.0 {
      assert value == -abs(x1[i]);
      assert value < 0.0;
    }
    result := result + [value];
    i := i + 1;
  }
}
// </vc-code>
