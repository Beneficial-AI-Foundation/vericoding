// <vc-preamble>
// Method to perform component-wise subtraction of two Chebyshev series
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method chebsub(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
    // Both input series must have the same length
    requires |c1| == |c2|
    
    // The result has the same length as the input series
    ensures |result| == |c1|
    
    // Component-wise subtraction property: each coefficient is the difference
    ensures forall i :: 0 <= i < |result| ==> result[i] == c1[i] - c2[i]
    
    // Anti-commutativity property can be expressed in terms of this method's behavior
    ensures forall i :: 0 <= i < |result| ==> 
        result[i] == -(c2[i] - c1[i])
    
    // Identity property: subtracting a series from itself yields zero coefficients
    ensures (c1 == c2) ==> (forall i :: 0 <= i < |result| ==> result[i] == 0.0)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |c1|
    invariant 0 <= i <= |c1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == c1[j] - c2[j]
  {
    result := result + [c1[i] - c2[i]];
    i := i + 1;
  }
}
// </vc-code>
