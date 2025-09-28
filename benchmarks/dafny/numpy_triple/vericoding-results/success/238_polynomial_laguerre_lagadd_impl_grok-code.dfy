// <vc-preamble>
// Add one Laguerre series to another
// Performs component-wise addition of two Laguerre series coefficients
// with zero padding for the shorter sequence
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method lagadd(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  // The result length is the maximum of the input lengths
  ensures |result| == (if |c1| >= |c2| then |c1| else |c2|)
  
  // Component-wise addition with zero padding
  ensures forall i :: 0 <= i < |result| ==>
    result[i] == (if i < |c1| then c1[i] else 0.0) + 
                 (if i < |c2| then c2[i] else 0.0)
  
  // Non-empty inputs produce non-empty output
  ensures (|c1| > 0 || |c2| > 0) ==> |result| > 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Implemented using a loop to build the result sequence with explicit bounds checks */
  var len := if |c1| >= |c2| then |c1| else |c2|;
  result := [];
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == (if k < |c1| then c1[k] else 0.0) + (if k < |c2| then c2[k] else 0.0)
  {
    var a := if i < |c1| then c1[i] else 0.0;
    var b := if i < |c2| then c2[i] else 0.0;
    result := result + [a + b];
    i := i + 1;
  }
}
// </vc-code>
