// <vc-preamble>
// Method that computes the logical AND of two boolean sequences element-wise
// Each element of the result is the logical AND of the corresponding elements from the input sequences
// </vc-preamble>

// <vc-helpers>
function logicalAndSeq(x1: seq<bool>, x2: seq<bool>): seq<bool>
  requires |x1| == |x2|
  ensures |logicalAndSeq(x1, x2)| == |x1|
  ensures forall i :: 0 <= i < |x1| ==> logicalAndSeq(x1, x2)[i] == (x1[i] && x2[i])
  decreases |x1|
{
  if |x1| == 0 then []
  else [x1[0] && x2[0]] + logicalAndSeq(x1[1..], x2[1..])
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
  result := logicalAndSeq(x1, x2);
}
// </vc-code>
