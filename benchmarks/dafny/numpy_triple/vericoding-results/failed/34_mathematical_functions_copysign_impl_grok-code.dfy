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
  /* code modified by LLM (iteration 5): Added mathematical equivalence loop invariant and abs preservation to prove the failing invariant */
  var i := 0;
  var res: seq<real> := [];
  while i < |x1|
    invariant i <= |x1| && |res| == i
    invariant forall k :: 0 <= k < i ==> abs(res[k]) == abs(x1[k])
    invariant forall k :: 0 <= k < i ==>
      (x2[k] >= 0.0 ==> res[k] >= 0.0) &&
      (x2[k] < 0.0 ==> res[k] < 0.0)
    invariant forall k :: 0 <= k < i ==> res[k] == abs(x1[k]) * sign(x2[k])
  {
    res := res + [abs(x1[i]) * sign(x2[i])];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
