// <vc-preamble>
// Helper function to compute power of a real number
ghost function Power(base: real, exp: nat): real
{
    if exp == 0 then 1.0
    else base * Power(base, exp - 1)
}

// Ghost function to evaluate a 3D polynomial at a single point
ghost function EvaluatePolynomial3D(
    x: real, y: real, z: real,
    coeffs: seq<seq<seq<real>>>,
    deg_x: nat, deg_y: nat, deg_z: nat
): real
    requires |coeffs| == deg_x + 1
    requires forall i :: 0 <= i < |coeffs| ==> |coeffs[i]| == deg_y + 1
    requires forall i :: 0 <= i < |coeffs| ==> 
        forall j :: 0 <= j < |coeffs[i]| ==> |coeffs[i][j]| == deg_z + 1
{
    SumOverIndices(x, y, z, coeffs, 0, 0, 0, deg_x, deg_y, deg_z)
}

// Helper ghost function to compute the triple sum
ghost function SumOverIndices(
    x: real, y: real, z: real,
    coeffs: seq<seq<seq<real>>>,
    i: nat, j: nat, k: nat,
    deg_x: nat, deg_y: nat, deg_z: nat
): real
    requires |coeffs| == deg_x + 1
    requires forall idx :: 0 <= idx < |coeffs| ==> |coeffs[idx]| == deg_y + 1
    requires forall idx :: 0 <= idx < |coeffs| ==> 
        forall jdx :: 0 <= jdx < |coeffs[idx]| ==> |coeffs[idx][jdx]| == deg_z + 1
    decreases deg_x - i, deg_y - j, deg_z - k
{
    if i > deg_x then 0.0
    else if j > deg_y then SumOverIndices(x, y, z, coeffs, i + 1, 0, 0, deg_x, deg_y, deg_z)
    else if k > deg_z then SumOverIndices(x, y, z, coeffs, i, j + 1, 0, deg_x, deg_y, deg_z)
    else
        coeffs[i][j][k] * Power(x, i) * Power(y, j) * Power(z, k) + 
        SumOverIndices(x, y, z, coeffs, i, j, k + 1, deg_x, deg_y, deg_z)
}

// Main method for 3D polynomial evaluation
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [changed 'function method' to 'method' to fix compilation error] */
method ComputePower(base: real, exp: nat) returns (r: real)
    ensures r == Power(base, exp)
{
    r := 1.0;
    var i: nat := 0;
    while i < exp
        invariant i <= exp
        invariant r == Power(base, i)
    {
        r := r * base;
        i := i + 1;
    }
}

/* helper modified by LLM (iteration 2): [updated to call ComputePower method correctly] */
method ComputeSumRecursive(x: real, y: real, z: real,
                           coeffs: seq<seq<seq<real>>>, 
                           i: nat, j: nat, k: nat,
                           deg_x: nat, deg_y: nat, deg_z: nat)
    returns (res: real)
    requires |coeffs| == deg_x + 1
    requires forall idx :: 0 <= idx < |coeffs| ==> |coeffs[idx]| == deg_y + 1
    requires forall idx :: 0 <= idx < |coeffs| ==> 
        forall jdx :: 0 <= jdx < |coeffs[idx]| ==> |coeffs[idx][jdx]| == deg_z + 1
    ensures res == SumOverIndices(x, y, z, coeffs, i, j, k, deg_x, deg_y, deg_z)
    decreases deg_x - i, deg_y - j, deg_z - k
{
    if i > deg_x {
        res := 0.0;
    } else if j > deg_y {
        res := ComputeSumRecursive(x, y, z, coeffs, i + 1, 0, 0, deg_x, deg_y, deg_z);
    } else if k > deg_z {
        res := ComputeSumRecursive(x, y, z, coeffs, i, j + 1, 0, deg_x, deg_y, deg_z);
    } else {
        var px := ComputePower(x, i);
        var py := ComputePower(y, j);
        var pz := ComputePower(z, k);
        var term_val := coeffs[i][j][k] * px * py * pz;
        var rest_val := ComputeSumRecursive(x, y, z, coeffs, i, j, k + 1, deg_x, deg_y, deg_z);
        res := term_val + rest_val;
    }
}

method ComputePolynomial3D(x: real, y: real, z: real,
                           coeffs: seq<seq<seq<real>>>, 
                           deg_x: nat, deg_y: nat, deg_z: nat)
    returns (res: real)
    requires |coeffs| == deg_x + 1
    requires forall i :: 0 <= i < |coeffs| ==> |coeffs[i]| == deg_y + 1
    requires forall i :: 0 <= i < |coeffs| ==> 
        forall j :: 0 <= j < |coeffs[i]| ==> |coeffs[i][j]| == deg_z + 1
    ensures res == EvaluatePolynomial3D(x, y, z, coeffs, deg_x, deg_y, deg_z)
{
    res := ComputeSumRecursive(x, y, z, coeffs, 0, 0, 0, deg_x, deg_y, deg_z);
}
// </vc-helpers>

// <vc-spec>
method Polyval3D(
    x: seq<real>, y: seq<real>, z: seq<real>,
    coeffs: seq<seq<seq<real>>>,
    deg_x: nat, deg_y: nat, deg_z: nat
) returns (result: seq<real>)
    requires |x| == |y| == |z|
    requires |coeffs| == deg_x + 1
    requires forall i :: 0 <= i < |coeffs| ==> |coeffs[i]| == deg_y + 1
    requires forall i :: 0 <= i < |coeffs| ==> 
        forall j :: 0 <= j < |coeffs[i]| ==> |coeffs[i][j]| == deg_z + 1
    ensures |result| == |x|
    ensures forall p :: 0 <= p < |result| ==> 
        result[p] == EvaluatePolynomial3D(x[p], y[p], z[p], coeffs, deg_x, deg_y, deg_z)
    ensures deg_x == 0 && deg_y == 0 && deg_z == 0 ==> 
        forall p :: 0 <= p < |result| ==> result[p] == coeffs[0][0][0]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [added array length invariant] */
  var res_array := new real[|x|];
  var p: nat := 0;
  while p < |x|
    invariant 0 <= p <= |x|
    invariant res_array.Length == |x|
    invariant forall i :: 0 <= i < p ==> 
        res_array[i] == EvaluatePolynomial3D(x[i], y[i], z[i], coeffs, deg_x, deg_y, deg_z)
  {
    var val := ComputePolynomial3D(x[p], y[p], z[p], coeffs, deg_x, deg_y, deg_z);
    res_array[p] := val;
    p := p + 1;
  }
  result := res_array[..];
}
// </vc-code>
