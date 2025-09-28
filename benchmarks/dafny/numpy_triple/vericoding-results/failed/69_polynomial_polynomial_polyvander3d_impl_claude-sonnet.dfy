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
// Helper function to compute column index in the 3D Vandermonde matrix
function computeColumnIndex(i: nat, j: nat, k: nat, yDeg: nat, zDeg: nat): nat
{
    (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k
}

/* helper modified by LLM (iteration 5): added stronger postcondition verification lemma */
lemma columnIndexBounds(i: nat, j: nat, k: nat, xDeg: nat, yDeg: nat, zDeg: nat)
    requires i <= xDeg && j <= yDeg && k <= zDeg
    ensures computeColumnIndex(i, j, k, yDeg, zDeg) < (xDeg + 1) * (yDeg + 1) * (zDeg + 1)
{
    var colIdx := computeColumnIndex(i, j, k, yDeg, zDeg);
    assert colIdx <= (yDeg + 1) * (zDeg + 1) * xDeg + (zDeg + 1) * yDeg + zDeg;
    assert (yDeg + 1) * (zDeg + 1) * xDeg + (zDeg + 1) * yDeg + zDeg < (xDeg + 1) * (yDeg + 1) * (zDeg + 1);
}

/* helper modified by LLM (iteration 5): lemma to verify postcondition holds for completed rows */
lemma rowSatisfiesPostcondition(row: seq<real>, p: int, x: seq<real>, y: seq<real>, z: seq<real>, xDeg: nat, yDeg: nat, zDeg: nat)
    requires 0 <= p < |x|
    requires |x| == |y| == |z|
    requires |row| == (xDeg + 1) * (yDeg + 1) * (zDeg + 1)
    requires forall i, j, k :: 0 <= i <= xDeg && 0 <= j <= yDeg && 0 <= k <= zDeg ==>
        var colIdx := computeColumnIndex(i, j, k, yDeg, zDeg);
        row[colIdx] == pow(x[p], i) * pow(y[p], j) * pow(z[p], k)
    ensures forall i :: 0 <= i <= xDeg ==>
        forall j :: 0 <= j <= yDeg ==>
            forall k :: 0 <= k <= zDeg ==>
                var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
                colIdx < (xDeg + 1) * (yDeg + 1) * (zDeg + 1) &&
                row[colIdx] == pow(x[p], i) * pow(y[p], j) * pow(z[p], k)
{
    forall i | 0 <= i <= xDeg
        ensures forall j :: 0 <= j <= yDeg ==>
            forall k :: 0 <= k <= zDeg ==>
                var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
                colIdx < (xDeg + 1) * (yDeg + 1) * (zDeg + 1) &&
                row[colIdx] == pow(x[p], i) * pow(y[p], j) * pow(z[p], k)
    {
        forall j | 0 <= j <= yDeg
            ensures forall k :: 0 <= k <= zDeg ==>
                var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
                colIdx < (xDeg + 1) * (yDeg + 1) * (zDeg + 1) &&
                row[colIdx] == pow(x[p], i) * pow(y[p], j) * pow(z[p], k)
        {
            forall k | 0 <= k <= zDeg
                ensures var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
                    colIdx < (xDeg + 1) * (yDeg + 1) * (zDeg + 1) &&
                    row[colIdx] == pow(x[p], i) * pow(y[p], j) * pow(z[p], k)
            {
                var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
                columnIndexBounds(i, j, k, xDeg, yDeg, zDeg);
                assert colIdx == computeColumnIndex(i, j, k, yDeg, zDeg);
            }
        }
    }
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
    /* code modified by LLM (iteration 5): added postcondition verification with helper lemma */
    var numPoints := |x|;
    var numCols := (xDeg + 1) * (yDeg + 1) * (zDeg + 1);
    
    V := [];
    
    var p := 0;
    while p < numPoints
        invariant 0 <= p <= numPoints
        invariant |V| == p
        invariant forall row :: 0 <= row < |V| ==> |V[row]| == numCols
        invariant forall row :: 0 <= row < |V| ==>
            forall i :: 0 <= i <= xDeg ==>
                forall j :: 0 <= j <= yDeg ==>
                    forall k :: 0 <= k <= zDeg ==>
                        var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
                        colIdx < (xDeg + 1) * (yDeg + 1) * (zDeg + 1) &&
                        V[row][colIdx] == pow(x[row], i) * pow(y[row], j) * pow(z[row], k)
    {
        var row := new real[numCols];
        
        var i := 0;
        while i <= xDeg
            invariant 0 <= i <= xDeg + 1
            invariant forall ii, jj, kk :: 0 <= ii < i && 0 <= jj <= yDeg && 0 <= kk <= zDeg ==>
                var colIdx := computeColumnIndex(ii, jj, kk, yDeg, zDeg);
                row[colIdx] == pow(x[p], ii) * pow(y[p], jj) * pow(z[p], kk)
        {
            var j := 0;
            while j <= yDeg
                invariant 0 <= j <= yDeg + 1
                invariant forall ii, jj, kk :: 0 <= ii < i && 0 <= jj <= yDeg && 0 <= kk <= zDeg ==>
                    var colIdx := computeColumnIndex(ii, jj, kk, yDeg, zDeg);
                    row[colIdx] == pow(x[p], ii) * pow(y[p], jj) * pow(z[p], kk)
                invariant forall jj, kk :: 0 <= jj < j && 0 <= kk <= zDeg ==>
                    var colIdx := computeColumnIndex(i, jj, kk, yDeg, zDeg);
                    row[colIdx] == pow(x[p], i) * pow(y[p], jj) * pow(z[p], kk)
            {
                var k := 0;
                while k <= zDeg
                    invariant 0 <= k <= zDeg + 1
                    invariant forall ii, jj, kk :: 0 <= ii < i && 0 <= jj <= yDeg && 0 <= kk <= zDeg ==>
                        var colIdx := computeColumnIndex(ii, jj, kk, yDeg, zDeg);
                        row[colIdx] == pow(x[p], ii) * pow(y[p], jj) * pow(z[p], kk)
                    invariant forall jj, kk :: 0 <= jj < j && 0 <= kk <= zDeg ==>
                        var colIdx := computeColumnIndex(i, jj, kk, yDeg, zDeg);
                        row[colIdx] == pow(x[p], i) * pow(y[p], jj) * pow(z[p], kk)
                    invariant forall kk :: 0 <= kk < k ==>
                        var colIdx := computeColumnIndex(i, j, kk, yDeg, zDeg);
                        row[colIdx] == pow(x[p], i) * pow(y[p], j) * pow(z[p], kk)
                {
                    var colIdx := computeColumnIndex(i, j, k, yDeg, zDeg);
                    columnIndexBounds(i, j, k, xDeg, yDeg, zDeg);
                    row[colIdx] := pow(x[p], i) * pow(y[p], j) * pow(z[p], k);
                    k := k + 1;
                }
                j := j + 1;
            }
            i := i + 1;
        }
        
        rowSatisfiesPostcondition(row[..], p, x, y, z, xDeg, yDeg, zDeg);
        V := V + [row[..]];
        p := p + 1;
    }
}
// </vc-code>
