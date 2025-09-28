// <vc-preamble>
// Method to perform component-wise subtraction of two Chebyshev series
// </vc-preamble>

// <vc-helpers>
function negateSeries(series: seq<real>): seq<real>
  requires series != []
  ensures |negateSeries(series)| == |series|
  ensures forall i :: 0 <= i < |series| ==> negateSeries(series)[i] == -series[i]
{
  seq(|series|, i requires 0 <= i < |series| => -series[i])
}

function subtractSeriesAtIndices(c1: seq<real>, c2: seq<real>, n: int): real
  requires |c1| == |c2|
  requires 0 <= n < |c1|
{
  c1[n] - c2[n]
}
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
  /* code modified by LLM (iteration 2): Fixed array/seq type mismatch */
  result := seq(|c1|, i requires 0 <= i < |c1| => c1[i] - c2[i]);
}
// </vc-code>
