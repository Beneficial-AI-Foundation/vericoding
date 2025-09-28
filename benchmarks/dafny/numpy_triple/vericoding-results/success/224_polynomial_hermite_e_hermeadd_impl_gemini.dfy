// <vc-preamble>
// Component-wise addition of two Hermite polynomial coefficient sequences
// Returns a sequence representing the sum of two Hermite series c1 + c2
// Coefficients are ordered from lowest to highest degree terms
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): made function total by moving precondition into guard */
function Get(s: seq<real>, i: int): real
{
  if i >= 0 && i < |s| then s[i] else 0.0
}
// </vc-helpers>

// <vc-spec>
method hermeadd(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  // The result length is the maximum of input lengths
  ensures |result| == if |c1| >= |c2| then |c1| else |c2|
  
  // Core coefficient addition property: each coefficient is sum of corresponding coefficients
  // Missing coefficients from shorter sequences are treated as zero
  ensures forall i :: 0 <= i < |result| ==>
    result[i] == (if i < |c1| then c1[i] else 0.0) + (if i < |c2| then c2[i] else 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): using total helper function to satisfy precondition proof */
  var n := if |c1| >= |c2| then |c1| else |c2|;
  result := seq(n, i => Get(c1, i) + Get(c2, i));
}
// </vc-code>
