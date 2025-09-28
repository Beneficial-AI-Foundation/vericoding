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
/* helper modified by LLM (iteration 5): dimension of Vandermonde */
function N(xD: nat, yD: nat, zD: nat): nat
{
  (xD + 1) * (yD + 1) * (zD + 1)
}

/* helper modified by LLM (iteration 5): column index encoding */
function col(yD: nat, zD: nat, i: nat, j: nat, k: nat): nat
{
  (yD + 1) * (zD + 1) * i + (zD + 1) * j + k
}

/* helper modified by LLM (iteration 5): decode i from a column index */
function IOf(yD: nat, zD: nat, idx: nat): nat
{
  idx / ((yD + 1) * (zD + 1))
}

/* helper modified by LLM (iteration 5): decode j from a column index */
function JOf(yD: nat, zD: nat, idx: nat): nat
{
  (idx % ((yD + 1) * (zD + 1))) / (zD + 1)
}

/* helper modified by LLM (iteration 5): decode k from a column index */
function KOf(yD: nat, zD: nat, idx: nat): nat
{
  (idx % ((yD + 1) * (zD + 1))) % (zD + 1)
}

/* helper modified by LLM (iteration 5): proof that encoding/decoding round-trips and index is in range */
lemma decode_col_roundtrip(xD: nat, yD: nat, zD: nat, i: nat, j: nat, k: nat)
  requires i <= xD && j <= yD && k <= zD
  ensures IOf(yD, zD, col(yD, zD, i, j, k)) == i
  ensures JOf(yD, zD, col(yD, zD, i, j, k)) == j
  ensures KOf(yD, zD, col(yD, zD, i, j, k)) == k
  ensures col(yD, zD, i, j, k) < N(xD, yD, zD)
{
  var yz := (yD + 1) * (zD + 1);
  assert yD + 1 > 0 && zD + 1 > 0;
  assert yz > 0;

  var rem := (zD + 1) * j + k;
  assert 0 <= rem;
  assert (zD + 1) * j <= (zD + 1) * yD;
  assert k <= zD;
  assert rem <= (zD + 1) * yD + zD;
  assert zD < zD + 1;
  assert rem < (zD + 1) * yD + (zD + 1);
  assert rem < yz;

  var c := yz * i + rem;
  assert c == col(yD, zD, i, j, k);

  assert 0 <= i;
  assert c / yz == i; // since 0 <= rem < yz and yz > 0
  assert c % yz == rem;

  assert 0 <= k && k < zD + 1;
  assert rem / (zD + 1) == j; // 0 <= k < zD+1
  assert rem % (zD + 1) == k;

  assert IOf(yD, zD, col(yD, zD, i, j, k)) == i;
  assert JOf(yD, zD, col(yD, zD, i, j, k)) == j;
  assert KOf(yD, zD, col(yD, zD, i, j, k)) == k;

  assert c < yz * (i + 1);
  assert i <= xD;
  assert i + 1 <= xD + 1;
  assert yz * (i + 1) <= yz * (xD + 1);
  assert c < yz * (xD + 1);
  assert yz * (xD + 1) == (xD + 1) * yz;
  assert N(xD, yD, zD) == (xD + 1) * yz;
  assert col(yD, zD, i, j, k) < N(xD, yD, zD);
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
  /* code modified by LLM (iteration 5): construct Vandermonde via sequence comprehensions and prove postconditions */
  var n := |x|;
  var cols := N(xDeg, yDeg, zDeg);
  V := seq(p | 0 <= p < n ::
        (seq(idx | 0 <= idx < cols ::
            pow(x[p], IOf(yDeg, zDeg, idx)) *
            pow(y[p], JOf(yDeg, zDeg, idx)) *
            pow(z[p], KOf(yDeg, zDeg, idx))
        ))
      );

  // Basic size properties
  assert |V| == n;
  assert forall p:nat | p < |V| :: |V[p]| == cols;

  // Pointwise characterization of rows
  assert forall p:nat | p < |x| ::
           V[p] ==
             (seq(idx | 0 <= idx < cols ::
                pow(x[p], IOf(yDeg, zDeg, idx)) *
                pow(y[p], JOf(yDeg, zDeg, idx)) *
                pow(z[p], KOf(yDeg, zDeg, idx))));

  // Main correctness property per entry
  assert forall p:nat, i:nat, j:nat, k:nat
         | p < |x| && i <= xDeg && j <= yDeg && k <= zDeg ::
         var colIdx := col(yDeg, zDeg, i, j, k);
         colIdx < cols &&
         V[p][colIdx] == pow(x[p], i) * pow(y[p], j) * pow(z[p], k)
    by
    {
      // Index within bounds
      decode_col_roundtrip(xDeg, yDeg, zDeg, i, j, k);
      assert col(yDeg, zDeg, i, j, k) < cols;
      // Access row p
      assert |V| == |x|;
      assert p < |V|;
      // Unfold row definition
      assert V[p] ==
        (seq(idx | 0 <= idx < cols ::
            pow(x[p], IOf(yDeg, zDeg, idx)) *
            pow(y[p], JOf(yDeg, zDeg, idx)) *
            pow(z[p], KOf(yDeg, zDeg, idx))));
      // Index the sequence at the encoded column
      assert V[p][col(yDeg, zDeg, i, j, k)] ==
            pow(x[p], IOf(yDeg, zDeg, col(yDeg, zDeg, i, j, k))) *
            pow(y[p], JOf(yDeg, zDeg, col(yDeg, zDeg, i, j, k))) *
            pow(z[p], KOf(yDeg, zDeg, col(yDeg, zDeg, i, j, k)));
      // Decode back to (i,j,k)
      assert IOf(yDeg, zDeg, col(yDeg, zDeg, i, j, k)) == i;
      assert JOf(yDeg, zDeg, col(yDeg, zDeg, i, j, k)) == j;
      assert KOf(yDeg, zDeg, col(yDeg, zDeg, i, j, k)) == k;
      // Conclude desired value
      assert V[p][col(yDeg, zDeg, i, j, k)] ==
             pow(x[p], i) * pow(y[p], j) * pow(z[p], k);
    }
}
// </vc-code>
