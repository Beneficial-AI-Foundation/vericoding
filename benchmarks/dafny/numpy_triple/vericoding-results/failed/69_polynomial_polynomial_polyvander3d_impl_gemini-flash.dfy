// <vc-preamble>
// Method to compute 3D polynomial Vandermonde matrix


// Helper function for exponentiation
function pow(base: real, exp: nat): real
{
    if exp == 0 then 1.0
    else base * pow(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added missing type to function declaration. */
function totalColumns(xDeg: nat, yDeg: nat, zDeg: nat): nat
{
    (xDeg + 1) * (yDeg + 1) * (zDeg + 1)
}
// </vc-helpers>

// <vc-spec>
method polyvander3d(x: seq<real>, y: seq<real>, z: seq<real>, xDeg: nat, yDeg: nat, zDeg: nat) 
    returns (V: seq<seq<real>>)
    requires |x| == |y| == |z|
    requires |x| > 0
    ensures |V| == |x|
    ensures forall p :: 0 <= p < |V| ==> |V[p]| == (xDeg + 1) * (yDeg + 1) * (zDeg + 1)
    ensures forall p :: 0 <= p < |x| ==>
        forall i :: 0 <= i <= xDeg ==>
            forall j :: 0 <= j <= yDeg ==>
                forall k :: 0 <= k <= zDeg ==>
                    var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
                    colIdx < (xDeg + 1) * (yDeg + 1) * (zDeg + 1) &&
                    V[p][colIdx] == pow(x[p], i) * pow(y[p], j) * pow(z[p], k)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed array initialization to create a sequence of sequences directly. */
{
    var N := |x|;
    var M := totalColumns(xDeg, yDeg, zDeg);
    var V_seq: seq<seq<real>> := new seq<real>[N](_ => new real[M]);

    var p := 0;
    while p < N
        invariant 0 <= p <= N
        invariant forall i :: 0 <= i < p ==> |V_seq[i]| == M
    {
        var row_arr: array<real> := new real[M];
        var colIdx := 0;
        var i := 0;
        while i <= xDeg
            invariant 0 <= i <= xDeg + 1
            invariant colIdx == i * ((yDeg + 1) * (zDeg + 1))
        {
            var j := 0;
            while j <= yDeg
                invariant 0 <= j <= yDeg + 1
                invariant colIdx == i * ((yDeg + 1) * (zDeg + 1)) + j * (zDeg + 1)
            {
                var k := 0;
                while k <= zDeg
                    invariant 0 <= k <= zDeg + 1
                    invariant colIdx == i * ((yDeg + 1) * (zDeg + 1)) + j * (zDeg + 1) + k
                {
                    row_arr[colIdx] := pow(x[p], i) * pow(y[p], j) * pow(z[p], k);
                    colIdx := colIdx + 1;
                    k := k + 1;
                }
                j := j + 1;
            }
            i := i + 1;
        }
        V_seq[p] := row_arr[..];
        p := p + 1;
    }

    return V_seq;
}
// </vc-code>
