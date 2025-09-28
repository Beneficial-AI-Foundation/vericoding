// <vc-preamble>
// Method that computes the logical AND of two boolean sequences element-wise
// Each element of the result is the logical AND of the corresponding elements from the input sequences
// </vc-preamble>

// <vc-helpers>
function SeqAnd(a: seq<bool>, b: seq<bool>): (c: seq<bool>)
  requires |a| == |b|
  ensures |c| == |a|
  ensures forall i :: 0 <= i < |c| ==> c[i] == (a[i] && b[i])
{
  if |a| == 0 then []
  else [a[0] && b[0]] + SeqAnd(a[1..], b[1..])
}

lemma SeqAndCommutative(a: seq<bool>, b: seq<bool>)
  requires |a| == |b|
  ensures SeqAnd(a, b) == SeqAnd(b, a)
  decreases |a|
{
  if |a| > 0 {
    SeqAndCommutative(a[1..], b[1..]);
  }
}

function AllTrueSeq(length: nat): (s: seq<bool>)
  ensures |s| == length
  ensures forall i :: 0 <= i < |s| ==> s[i]
  decreases length
{
  if length == 0 then []
  else [true] + AllTrueSeq(length - 1)
}

function AllFalseSeq(length: nat): (s: seq<bool>)
  ensures |s| == length
  ensures forall i :: 0 <= i < |s| ==> !s[i]
  decreases length
{
  if length == 0 then []
  else [false] + AllFalseSeq(length - 1)
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
  /* code modified by LLM (iteration 2): fixed loop invariants and sequence indexing */
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (x1[j] && x2[j])
  {
    result := result + [x1[i] && x2[i]];
    i := i + 1;
  }
}
// </vc-code>
