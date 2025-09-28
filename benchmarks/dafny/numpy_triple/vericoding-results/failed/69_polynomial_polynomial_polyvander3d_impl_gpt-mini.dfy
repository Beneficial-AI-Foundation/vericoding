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
/* helper modified by LLM (iteration 5): powi for int exponent */
function powi(base: real, exp: int): real
  requires exp >= 0
{
  if exp == 0 then 1.0 else base * powi(base, exp - 1)
}

/* helper modified by LLM (iteration 5): element constructor for a row given linear column index */
function Row3_elem(xp: real, yp: real, zp: real, xDeg: nat, yDeg: nat, zDeg: nat, col: nat): real
  requires col < (xDeg + 1) * (yDeg + 1) * (zDeg + 1)
{
  var m := (yDeg + 1) * (zDeg + 1);
  var i := col / m;
  var rem := col % m;
  var j := rem / (zDeg + 1);
  var k := rem % (zDeg + 1);
  pow(xp, i) * pow(yp, j) * pow(zp, k)
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
{
  /* code modified by LLM (iteration 5): build Vandermonde matrix rows using arrays and pow */
  var n := |x|;
  var m := (xDeg + 1) * (yDeg + 1) * (zDeg + 1);
  V := [];
  var p: int := 0;
  while p < n
    invariant 0 <= p <= n
    invariant |V| == p
  {
    var row := new real[m];
    var col: nat := 0;
    var m2 := (yDeg + 1) * (zDeg + 1);
    while col < m
      invariant 0 <= col <= m
    {
      var i := col / m2;
      var rem := col % m2;
      var j := rem / (zDeg + 1);
      var k := rem % (zDeg + 1);
      row[col] := pow(x[p], i) * pow(y[p], j) * pow(z[p], k);
      col := col + 1;
    }
    V := V + [row[..]];
    p := p + 1;
  }
}

// </vc-code>
