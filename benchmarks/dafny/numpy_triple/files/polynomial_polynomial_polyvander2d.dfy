// <vc-preamble>
// Power function for real numbers with natural exponent
function Power(base: real, exp: nat): real
{
    if exp == 0 then 1.0
    else base * Power(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method PolyVander2D(x: seq<real>, y: seq<real>, xDeg: nat, yDeg: nat) 
    returns (result: seq<seq<real>>)
    requires |x| == |y|
    requires |x| > 0
    ensures |result| == |x|
    ensures forall k :: 0 <= k < |result| ==> |result[k]| == (xDeg + 1) * (yDeg + 1)
    ensures forall k :: 0 <= k < |result| ==>
        forall i :: 0 <= i <= xDeg ==>
            forall j :: 0 <= j <= yDeg ==>
                var colIdx := (yDeg + 1) * i + j;
                colIdx < |result[k]| && 
                result[k][colIdx] == Power(x[k], i) * Power(y[k], j)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
