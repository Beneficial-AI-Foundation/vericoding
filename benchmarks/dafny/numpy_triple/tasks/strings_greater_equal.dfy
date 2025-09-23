// <vc-preamble>
/*
 * Dafny specification for numpy.strings.greater_equal
 * 
 * Performs element-wise lexicographic string comparison, returning a boolean sequence
 * indicating whether each string in x1 is greater than or equal to the corresponding 
 * string in x2.
 */

// Helper function for lexicographic string comparison
function LexGreaterEqual(s1: string, s2: string): bool
{
  if |s1| == 0 then true
  else if |s2| == 0 then true
  else if s1[0] > s2[0] then true
  else if s1[0] < s2[0] then false
  else LexGreaterEqual(s1[1..], s2[1..])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method GreaterEqual(x1: seq<string>, x2: seq<string>) returns (result: seq<bool>)
  // Precondition: input sequences must have the same length
  requires |x1| == |x2|
  
  // Postcondition: result has same length as inputs
  ensures |result| == |x1|
  
  // Core property: element-wise lexicographic comparison
  ensures forall i :: 0 <= i < |result| ==> result[i] == LexGreaterEqual(x1[i], x2[i])
  
  // Reflexive property: every string is >= itself
  ensures forall i :: 0 <= i < |x1| && x1[i] == x2[i] ==> result[i] == true
  
  // Antisymmetric property: if s1 >= s2 and s2 >= s1, then s1 == s2
  ensures forall i :: 0 <= i < |x1| && LexGreaterEqual(x1[i], x2[i]) && LexGreaterEqual(x2[i], x1[i]) ==> x1[i] == x2[i]
  
  // Empty string properties: empty string is <= any string, any string is >= empty string
  ensures forall i :: 0 <= i < |x1| && x1[i] == "" && x2[i] == "" ==> result[i] == true
  ensures forall i :: 0 <= i < |x1| && x1[i] != "" && x2[i] == "" ==> result[i] == true
  
  // Deterministic property: function behavior is deterministic
  ensures forall y1: seq<string>, y2: seq<string> :: |y1| == |x1| && |y2| == |x2| && y1 == x1 && y2 == x2 ==>
    exists r: seq<bool> :: |r| == |result| && (forall j :: 0 <= j < |r| ==> r[j] == LexGreaterEqual(y1[j], y2[j]))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
