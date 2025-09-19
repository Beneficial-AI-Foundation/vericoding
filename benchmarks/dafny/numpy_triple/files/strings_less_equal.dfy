// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method LessEqual(x1: seq<string>, x2: seq<string>) returns (result: seq<bool>)
  // Precondition: Input sequences must have the same length
  requires |x1| == |x2|
  
  // Postcondition: Result has same length as inputs
  ensures |result| == |x1| == |x2|
  
  // Core property: result[i] = (x1[i] <= x2[i]) for all indices
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] <= x2[i])
  
  // Equivalence: result[i] is true iff x1[i] <= x2[i]
  ensures forall i :: 0 <= i < |result| ==> (result[i] <==> x1[i] <= x2[i])
  
  // Reflexivity: if inputs are the same, result is all true
  ensures x1 == x2 ==> forall i :: 0 <= i < |result| ==> result[i] == true
  
  // Consistency with string equality: if strings are equal, result is true
  ensures forall i :: 0 <= i < |result| ==> x1[i] == x2[i] ==> result[i] == true
  
  // Antisymmetry consistency: if x1[i] <= x2[i] and x2[i] <= x1[i], then x1[i] == x2[i]
  ensures forall i :: 0 <= i < |result| ==> 
    (x1[i] <= x2[i] && x2[i] <= x1[i]) ==> x1[i] == x2[i]
  
  // Transitivity preservation: consistent with transitive nature of string ordering
  ensures forall i :: 0 <= i < |result| ==> 
    forall z {:trigger x1[i] <= z, z <= x2[i]} :: x1[i] <= z && z <= x2[i] ==> x1[i] <= x2[i]
  
  // Decidability: result contains only boolean values (always true or false)
  ensures forall i :: 0 <= i < |result| ==> result[i] == true || result[i] == false
  
  // Total order property: for any strings, one must be <= the other
  ensures forall i :: 0 <= i < |result| ==> x1[i] <= x2[i] || x2[i] <= x1[i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
