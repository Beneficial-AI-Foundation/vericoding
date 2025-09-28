// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed unnecessary lemmas; provide trivial lemma */
lemma TrivialLemma()
  ensures true
{}

// </vc-helpers>

// <vc-spec>
method BitwiseAnd(x1: seq<bv32>, x2: seq<bv32>) returns (result: seq<bv32>)
  // Arrays must have the same length
  requires |x1| == |x2|
  
  // Result has same length as inputs
  ensures |result| == |x1|
  
  // Each element is the bitwise AND of corresponding input elements
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] & x2[i])
  
  // Bitwise AND result is always <= both inputs (for non-negative integers)
  ensures forall i :: 0 <= i < |result| ==> result[i] <= x1[i]
  ensures forall i :: 0 <= i < |result| ==> result[i] <= x2[i]
  
  // Annihilator property: if either input is zero, result is zero
  ensures forall i :: 0 <= i < |result| ==> (x1[i] == 0 || x2[i] == 0) ==> result[i] == 0
  
  // Idempotence: x & x = x
  ensures forall i :: 0 <= i < |result| ==> (x1[i] == x2[i] ==> result[i] == x1[i])
  
  // Commutativity property (implicitly satisfied by bitwise AND)
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x2[i] & x1[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): construct the result sequence with a loop instead of a comprehension */
  var n := |x1|;
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (x1[j] & x2[j])
  {
    result := result + [x1[i] & x2[i]];
    i := i + 1;
  }
}
// </vc-code>
