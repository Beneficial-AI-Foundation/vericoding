// <vc-preamble>
// Method to add two Legendre series by component-wise addition of coefficients
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LegendreAdd(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
    // The result has length equal to the maximum of the input lengths
    ensures |result| == if |c1| >= |c2| then |c1| else |c2|
    // Each coefficient in the result is the sum of corresponding coefficients from inputs
    // Missing coefficients are treated as zero
    ensures forall i :: 0 <= i < |result| ==> 
        result[i] == (if i < |c1| then c1[i] else 0.0) + (if i < |c2| then c2[i] else 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): use array to build sequence */
  var n := if |c1| >= |c2| then |c1| else |c2|;
  var a := new real[n];
  for i := 0 to n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == (if j < |c1| then c1[j] else 0.0) + (if j < |c2| then c2[j] else 0.0)
  {
    a[i] := (if i < |c1| then c1[i] else 0.0) + (if i < |c2| then c2[i] else 0.0);
  }
  result := a[..];
}
// </vc-code>
