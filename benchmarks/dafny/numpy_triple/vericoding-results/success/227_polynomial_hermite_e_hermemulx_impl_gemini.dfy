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
  /* code modified by LLM (iteration 5): [added loop invariant on index i to resolve compilation error] */
  if |c| == 0 {
    result := [0.0];
  } else {
    var res := new real[|c| + 1];
    res[0] := 0.0;

    if |c| >= 1 {
        res[1] := c[0] + (if |c| > 1 then c[1] else 0.0);
    }

    var i := 2;
    while i < |c| + 1
        invariant res.Length == |c| + 1
        invariant 2 <= i <= |c| + 1
        invariant res[0] == 0.0
        invariant |c| > 0 ==> res[1] == c[0] + (if |c| > 1 then c[1] else 0.0)
        invariant forall k :: 2 <= k < i ==> 
            res[k] == (if k-1 >= 0 && k-1 < |c| then c[k-1] else 0.0) + 
                      (if k+1 < |c| then ((k-1) as real) * c[k+1] else 0.0)
    {
        var term1 := if i - 1 < |c| then c[i-1] else 0.0;
        var term2 := if i + 1 < |c| then ((i-1) as real) * c[i+1] else 0.0;
        res[i] := term1 + term2;
        i := i + 1;
    }
    result := res[..];
  }
}
// </vc-code>
