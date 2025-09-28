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
/* helper modified by LLM (iteration 3): Added lemma to help verify column index bounds */
lemma ColIdxBounds(i: nat, j: nat, k: nat, xDeg: nat, yDeg: nat, zDeg: nat)
  requires i <= xDeg && j <= yDeg && k <= zDeg
  ensures var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
          colIdx < (xDeg + 1) * (yDeg + 1) * (zDeg + 1)
{
  var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
  assert colIdx <= (yDeg + 1) * (zDeg + 1) * xDeg + (zDeg + 1) * yDeg + zDeg;
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
  /* code modified by LLM (iteration 3): Added comprehensive invariants to verify matrix values */
  V := [];
  var p := 0;
  while p < |x|
    invariant 0 <= p <= |x|
    invariant |V| == p
    invariant forall q :: 0 <= q < p ==> |V[q]| == (xDeg + 1) * (yDeg + 1) * (zDeg + 1)
    invariant forall q :: 0 <= q < p ==>
        forall i :: 0 <= i <= xDeg ==>
            forall j :: 0 <= j <= yDeg ==>
                forall k :: 0 <= k <= zDeg ==>
                    var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + k;
                    V[q][colIdx] == pow(x[q], i) * pow(y[q], j) * pow(z[q], k)
  {
    var row := [];
    var i := 0;
    while i <= xDeg
      invariant 0 <= i <= xDeg + 1
      invariant |row| == i * (yDeg + 1) * (zDeg + 1)
      invariant forall ii :: 0 <= ii < i ==>
          forall jj :: 0 <= jj <= yDeg ==>
              forall kk :: 0 <= kk <= zDeg ==>
                  var colIdx := (yDeg + 1) * (zDeg + 1) * ii + (zDeg + 1) * jj + kk;
                  colIdx < |row| && row[colIdx] == pow(x[p], ii) * pow(y[p], jj) * pow(z[p], kk)
    {
      var j := 0;
      while j <= yDeg
        invariant 0 <= j <= yDeg + 1
        invariant |row| == i * (yDeg + 1) * (zDeg + 1) + j * (zDeg + 1)
        invariant forall ii :: 0 <= ii < i ==>
            forall jj :: 0 <= jj <= yDeg ==>
                forall kk :: 0 <= kk <= zDeg ==>
                    var colIdx := (yDeg + 1) * (zDeg + 1) * ii + (zDeg + 1) * jj + kk;
                    colIdx < |row| && row[colIdx] == pow(x[p], ii) * pow(y[p], jj) * pow(z[p], kk)
        invariant forall jj :: 0 <= jj < j ==>
            forall kk :: 0 <= kk <= zDeg ==>
                var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * jj + kk;
                colIdx < |row| && row[colIdx] == pow(x[p], i) * pow(y[p], jj) * pow(z[p], kk)
      {
        var k := 0;
        while k <= zDeg
          invariant 0 <= k <= zDeg + 1
          invariant |row| == i * (yDeg + 1) * (zDeg + 1) + j * (zDeg + 1) + k
          invariant forall ii :: 0 <= ii < i ==>
              forall jj :: 0 <= jj <= yDeg ==>
                  forall kk :: 0 <= kk <= zDeg ==>
                      var colIdx := (yDeg + 1) * (zDeg + 1) * ii + (zDeg + 1) * jj + kk;
                      colIdx < |row| && row[colIdx] == pow(x[p], ii) * pow(y[p], jj) * pow(z[p], kk)
          invariant forall jj :: 0 <= jj < j ==>
              forall kk :: 0 <= kk <= zDeg ==>
                  var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * jj + kk;
                  colIdx < |row| && row[colIdx] == pow(x[p], i) * pow(y[p], jj) * pow(z[p], kk)
          invariant forall kk :: 0 <= kk < k ==>
              var colIdx := (yDeg + 1) * (zDeg + 1) * i + (zDeg + 1) * j + kk;
              colIdx < |row| && row[colIdx] == pow(x[p], i) * pow(y[p], j) * pow(z[p], kk)
        {
          row := row + [pow(x[p], i) * pow(y[p], j) * pow(z[p], k)];
          k := k + 1;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    assert |row| == (xDeg + 1) * (yDeg + 1) * (zDeg + 1);
    V := V + [row];
    p := p + 1;
  }
}
// </vc-code>
