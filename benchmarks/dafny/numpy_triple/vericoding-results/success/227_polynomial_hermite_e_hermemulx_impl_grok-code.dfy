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
  result := [];
  var i := 0;
  while i < |c| + 1
    invariant i <= |c| + 1
    invariant |result| == i
    invariant forall j :: 0 <= j < |result| ==>
      (j == 0 ==> result[0] == 0.0) &&
      (j == 1 && |c| > 0 ==> result[1] == c[0] + (if |c| > 1 then c[1] else 0.0)) &&
      (j >= 2 ==> result[j] == (if j-1 >= 0 && j-1 < |c| then c[j-1] else 0.0) + (if j+1 < |c| then ((j-1) as real) * c[j+1] else 0.0))
  {
    var val: real;
    if i == 0 {
      val := 0.0;
    } else if i == 1 {
      val := c[0] + (if |c| > 1 then c[1] else 0.0);
    } else {
      val := (if i-1 >= 0 && i-1 < |c| then c[i-1] else 0.0) + (if i+1 < |c| then ((i-1) as real) * c[i+1] else 0.0);
    }
    result := result + [val];
    i := i + 1;
  }
}
// </vc-code>
