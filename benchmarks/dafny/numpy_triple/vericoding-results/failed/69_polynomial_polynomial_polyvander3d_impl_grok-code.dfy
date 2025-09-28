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
/* helper modified by LLM (iteration 5): inlined GetIJK and ComputeValue computation to avoid verification timeout */
function ComputeRow(xp: real, yp: real, zp: real, xDeg: nat, yDeg: nat, zDeg: nat): seq<real>
  ensures |ComputeRow(xp, yp, zp, xDeg, yDeg, zDeg)| == (xDeg + 1) * (yDeg + 1) * (zDeg + 1)
  ensures forall i {:trigger} :: 0 <= i <= xDeg ==>
    forall j {:trigger} :: 0 <= j <= yDeg ==>
      forall k {:trigger} :: 0 <= k <= zDeg ==>
        var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
        colIdx < (xDeg + 1) * (yDeg + 1) * (zDeg + 1) &&
        ComputeRow(xp, yp, zp, xDeg, yDeg, zDeg)[colIdx] == pow(xp, i) * pow(yp, j) * pow(zp, k)
{
  var total := (xDeg + 1) * (yDeg + 1) * (zDeg + 1);
  var zSize := zDeg + 1;
  var yzSize := (yDeg + 1) * zSize;
  seq(total, (col: nat) requires 0 <= col < total =>
    var i := col / yzSize;
    var rem := col % yzSize;
    var j := rem / zSize;
    var k := rem % zSize;
    pow(xp, i) * pow(yp, j) * pow(zp, k)
  )
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
/* code modified by LLM (iteration 5): implementation retained */
{
  V := seq(|x|, (p: nat) requires 0 <= p < |x| => 
    ComputeRow(x[p], y[p], z[p], xDeg, yDeg, zDeg)
  );
}
// </vc-code>
