// <vc-preamble>
// Method to multiply a Hermite series by x
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HermeMulX(c: seq<real>) returns (result: seq<real>)
  requires |c| >= 0
  ensures |result| == |c| + 1
  // The first coefficient is always 0
  ensures |result| > 0 ==> result[0] == 0.0
  // For the second coefficient: c[0] plus c[1] if it exists
  ensures |c| > 0 && |result| > 1 ==> result[1] == c[0] + (if |c| > 1 then 1.0 * c[1] else 0.0)
  // General recursion relationship: result[i] = c[i-1] + (i-1)*c[i+1] with bounds checking
  ensures forall i :: 2 <= i < |result| ==> 
    result[i] == (if i-1 >= 0 && i-1 < |c| then c[i-1] else 0.0) + 
                 (if i+1 < |c| then ((i-1) as real) * c[i+1] else 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed array vs sequence type error */
  if |c| == 0 {
    result := [0.0];
  } else {
    var temp := new real[|c| + 1];
    temp[0] := 0.0;
    
    if |c| > 0 {
      temp[1] := c[0] + (if |c| > 1 then 1.0 * c[1] else 0.0);
    }
    
    var i := 2;
    while i < |c| + 1
      invariant 0 <= i <= |c| + 1
      invariant temp[0] == 0.0
      invariant |c| > 0 && |c| + 1 > 1 ==> temp[1] == c[0] + (if |c| > 1 then 1.0 * c[1] else 0.0)
      invariant forall j :: 2 <= j < i ==> 
        temp[j] == (if j-1 >= 0 && j-1 < |c| then c[j-1] else 0.0) + 
                   (if j+1 < |c| then ((j-1) as real) * c[j+1] else 0.0)
    {
      temp[i] := (if i-1 >= 0 && i-1 < |c| then c[i-1] else 0.0) + 
                 (if i+1 < |c| then ((i-1) as real) * c[i+1] else 0.0);
      i := i + 1;
    }
    result := temp[..];
  }
}
// </vc-code>
