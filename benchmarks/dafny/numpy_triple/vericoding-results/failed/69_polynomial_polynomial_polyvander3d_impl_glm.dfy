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
function TotalColumns(xDeg: nat, yDeg: nat, zDeg: nat): nat
{
    (xDeg + 1) * (yDeg + 1) * (zDeg + 1)
}

function ColumnIndex(i: nat, j: nat, k: nat, yDeg: nat, zDeg: nat): nat
{
    (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k
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
/* code modified by LLM (iteration 2): fixed type mismatch and unresolved identifiers by using intermediate array and converting to sequence */
{
  var totalCols := TotalColumns(xDeg, yDeg, zDeg);
  var arrayV := new real[|x|][totalCols];
  for p := 0 to |x|-1
    for i := 0 to xDeg
      for j := 0 to yDeg
        for k := 0 to zDeg
          var col := ColumnIndex(i, j, k, yDeg, zDeg);
          arrayV[p][col] := pow(x[p], i) * pow(y[p], j) * pow(z[p], k);
  V := seq(|x|, p => seq(totalCols, col => arrayV[p][col]));
}
// </vc-code>
