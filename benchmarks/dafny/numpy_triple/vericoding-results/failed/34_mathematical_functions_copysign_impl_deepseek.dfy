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
function copysign_element(x1: real, x2: real): real
  ensures copysign_element(x1, x2) == abs(x1) * sign(x2)
  ensures abs(copysign_element(x1, x2)) == abs(x1)
  ensures (x2 >= 0.0 ==> copysign_element(x1, x2) >= 0.0) && (x2 < 0.0 ==> copysign_element(x1, x2) < 0.0)
{
  if x2 >= 0.0 then abs(x1) else -abs(x1)
}

lemma copysign_element_properties(x1: real, x2: real)
  ensures copysign_element(x1, x2) == abs(x1) * sign(x2)
  ensures abs(copysign_element(x1, x2)) == abs(x1)
  ensures (x2 >= 0.0 ==> copysign_element(x1, x2) >= 0.0) && (x2 < 0.0 ==> copysign_element(x1, x2) < 0.0)
{
  /* helper modified by LLM (iteration 5): fixed negative case to prove sign condition */
  if x2 >= 0.0 {
    assert sign(x2) == 1.0;
    assert copysign_element(x1, x2) == abs(x1) == abs(x1) * 1.0;
    assert copysign_element(x1, x2) >= 0.0;
  } else {
    assert sign(x2) == -1.0;
    assert copysign_element(x1, x2) == -abs(x1) == abs(x1) * -1.0;
    assert copysign_element(x1, x2) < 0.0;
    assert -abs(x1) < 0.0; // Explicit negative proof
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
  /* code modified by LLM (iteration 5): iterative implementation using helper */
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == copysign_element(x1[j], x2[j])
  {
    result := result + [copysign_element(x1[i], x2[i])];
    i := i + 1;
  }
}
// </vc-code>
