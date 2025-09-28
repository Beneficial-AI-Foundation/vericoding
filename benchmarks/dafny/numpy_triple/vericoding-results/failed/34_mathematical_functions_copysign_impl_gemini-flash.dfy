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
/* For the current problem, no additional helper functions are needed. The existing `abs` and `sign` functions in the preamble are sufficient and correctly defined. */
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
/* code modified by LLM (iteration 5): The loop condition in the previous attempt was correct as 0 to |x1|-1. However, the error message 'lower bound must not exceed upper bound' indicates an issue with an empty sequence where |x1| is 0, causing |x1|-1 to be -1, making 0 > -1. The fix is to add a check for an empty sequence and handle it by returning an empty result. */
{
  if |x1| == 0 {
    result := [];
    return;
  }

  var tempResult: seq<real> := [];
  for i := 0 to |x1|-1
    invariant 0 <= i <= |x1|
    invariant |tempResult| == i
    invariant forall j :: 0 <= j < i ==> tempResult[j] == abs(x1[j]) * sign(x2[j])
  {
    var currentElement := abs(x1[i]) * sign(x2[i]);
    tempResult := tempResult + [currentElement];
  }
  result := tempResult;
}
// </vc-code>
