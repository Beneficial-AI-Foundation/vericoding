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
/* helper modified by LLM (iteration 5): Remove unused helpers and focus on core functionality */
function termValue(x: real, y: real, z: real, i: nat, j: nat, k: nat): real 
{
  pow(x, i) * pow(y, j) * pow(z, k)
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
/* code modified by LLM (iteration 5): Fix array initialization and seq conversion */
{
  var n := |x|;
  var cols := (xDeg + 1) * (yDeg + 1) * (zDeg + 1);
  V := [];
  
  var p := 0;
  while p < n
    invariant 0 <= p <= n
    invariant |V| == p
  {
    var row_array := new real[cols];
    var row: seq<real> := [];
    
    var i: nat := 0;
    while i <= xDeg
      invariant 0 <= i <= xDeg + 1
    {
      var j: nat := 0;
      while j <= yDeg
        invariant 0 <= j <= yDeg + 1
      {
        var k: nat := 0;
        while k <= zDeg
          invariant 0 <= k <= zDeg + 1
        {
          var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
          row_array[colIdx] := termValue(x[p], y[p], z[p], i, j, k);
          k := k + 1;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    
    row := ConvertArrayToSeq(row_array);
    V := V + [row];
    p := p + 1;
  }
}
// </vc-code>
