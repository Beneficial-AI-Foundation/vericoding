// <vc-preamble>
// Method to add two Legendre series by component-wise addition of coefficients
// </vc-preamble>

// <vc-helpers>
function GetCoeff(s: seq<real>, i: nat): real { if i < |s| then s[i] else 0.0 }
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
  var n := if |c1| >= |c2| then |c1| else |c2|;
  var res_array := new real[n];
  forall i | 0 <= i < n 
  {
    res_array[i] := GetCoeff(c1, i) + GetCoeff(c2, i);
  }
  result := res_array[..];
}
// </vc-code>
