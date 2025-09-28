// <vc-preamble>
// Component-wise addition of two Hermite polynomial coefficient sequences
// Returns a sequence representing the sum of two Hermite series c1 + c2
// Coefficients are ordered from lowest to highest degree terms
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 3): Add loop invariants to prove length and coefficient postconditions */
  var len := if |c1| >= |c2| then |c1| else |c2|;
  result := [];
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (if j < |c1| then c1[j] else 0.0) + (if j < |c2| then c2[j] else 0.0)
  {
    var coeff1 := if i < |c1| then c1[i] else 0.0;
    var coeff2 := if i < |c2| then c2[i] else 0.0;
    result := result + [coeff1 + coeff2];
    i := i + 1;
  }
}
// </vc-code>
