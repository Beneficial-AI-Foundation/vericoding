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
/* helper modified by LLM (iteration 3): Fixed copysignElement properties to handle zero magnitude case */
function copysignElement(mag: real, sgn: real): real
{
  abs(mag) * sign(sgn)
}

lemma CopysignElementProperties(mag: real, sgn: real)
  ensures sgn >= 0.0 ==> copysignElement(mag, sgn) == abs(mag)
  ensures sgn < 0.0 ==> copysignElement(mag, sgn) == -abs(mag)
  ensures abs(copysignElement(mag, sgn)) == abs(mag)
  ensures sgn >= 0.0 ==> copysignElement(mag, sgn) >= 0.0
  ensures sgn < 0.0 && mag != 0.0 ==> copysignElement(mag, sgn) < 0.0
  ensures sgn < 0.0 && mag == 0.0 ==> copysignElement(mag, sgn) == 0.0
  ensures copysignElement(mag, sgn) == abs(mag) * sign(sgn)
{
  // The body is empty as these follow directly from the definitions
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
  /* code modified by LLM (iteration 3): Adjusted invariants to handle zero case correctly */
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
      (x2[j] < 0.0 && x1[j] != 0.0 ==> result[j] < 0.0) &&
      (x2[j] < 0.0 && x1[j] == 0.0 ==> result[j] == 0.0)
    invariant forall j :: 0 <= j < i ==>
      result[j] == abs(x1[j]) * sign(x2[j])
  {
    CopysignElementProperties(x1[i], x2[i]);
    result := result + [copysignElement(x1[i], x2[i])];
    i := i + 1;
  }
}
// </vc-code>
