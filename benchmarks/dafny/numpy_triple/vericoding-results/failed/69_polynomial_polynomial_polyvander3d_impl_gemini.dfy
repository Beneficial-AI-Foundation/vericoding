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
method ComputeRow(xp: real, yp: real, zp: real, xDeg: nat, yDeg: nat, zDeg: nat)
    returns (row: seq<real>)
    ensures |row| == (xDeg + 1) * (yDeg + 1) * (zDeg + 1)
    ensures forall i :: 0 <= i <= xDeg ==>
            forall j :: 0 <= j <= yDeg ==>
                forall k :: 0 <= k <= zDeg ==>
                    var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
                    colIdx < |row| &&
                    row[colIdx] == pow(xp, i) * pow(yp, j) * pow(zp, k)
{
    var num_cols := (xDeg + 1) * (yDeg + 1) * (zDeg + 1);
    var arr := new real[num_cols];
    
    var YZ_size := (yDeg + 1) * (zDeg + 1);
    var Z_size := (zDeg + 1);

    var i := 0;
    while i <= xDeg
        invariant 0 <= i <= xDeg + 1
        invariant forall i_prime, j_prime, k_prime :: 0 <= i_prime < i && 0 <= j_prime <= yDeg && 0 <= k_prime <= zDeg ==>
                    let colIdx := YZ_size * i_prime + Z_size * j_prime + k_prime in
                    arr[colIdx] == pow(xp, i_prime) * pow(yp, j_prime) * pow(zp, k_prime)
    {
        var xp_i := pow(xp, i);
        var j := 0;
        while j <= yDeg
            invariant 0 <= j <= yDeg + 1
            invariant forall j_prime, k_prime :: 0 <= j_prime < j && 0 <= k_prime <= zDeg ==>
                        let colIdx := YZ_size * i + Z_size * j_prime + k_prime in
                        arr[colIdx] == xp_i * pow(yp, j_prime) * pow(zp, k_prime)
        {
            var yp_j := pow(yp, j);
            var k := 0;
            while k <= zDeg
                invariant 0 <= k <= zDeg + 1
                invariant forall k_prime :: 0 <= k_prime < k ==>
                            let colIdx := YZ_size * i + Z_size * j + k_prime in
                            arr[colIdx] == xp_i * yp_j * pow(zp, k_prime)
            {
                var colIdx := YZ_size * i + Z_size * j + k;
                arr[colIdx] := xp_i * yp_j * pow(zp, k);
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    row := arr[..];
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
    V := [];
    var p: nat := 0;
    while p < |x|
        invariant 0 <= p <= |x|
        invariant |V| == p
        invariant forall pp :: 0 <= pp < p ==> |V[pp]| == (xDeg + 1) * (yDeg + 1) * (zDeg + 1)
        invariant forall pp :: 0 <= pp < p ==>
            forall i :: 0 <= i <= xDeg ==>
            forall j :: 0 <= j <= yDeg ==>
                forall k :: 0 <= k <= zDeg ==>
                    var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
                    colIdx < |V[pp]| && V[pp][colIdx] == pow(x[pp], i) * pow(y[pp], j) * pow(z[pp], k)
    {
        var new_row := ComputeRow(x[p], y[p], z[p], xDeg, yDeg, zDeg);
        V := V + [new_row];
        p := p + 1;
    }
}
// </vc-code>
