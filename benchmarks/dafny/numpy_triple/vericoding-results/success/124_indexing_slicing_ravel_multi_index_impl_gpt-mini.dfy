// <vc-preamble>
// Main method that converts 2D multi-indices to flat indices
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): ensure product bound lemma */
lemma MulAddLessThan(rows: nat, cols: nat, a: nat, c: nat)
  requires rows > 0 && cols > 0
  requires a < rows && c < cols
  ensures a * cols + c < rows * cols
{
  assert a <= rows - 1;
  assert c <= cols - 1;
  calc {
    a * cols + c;
    <= (rows - 1) * cols + c;
    <= (rows - 1) * cols + (cols - 1);
    == rows * cols - 1;
    < rows * cols;
  }
}

// </vc-helpers>

// <vc-spec>
method RavelMultiIndex(rowIndices: seq<nat>, colIndices: seq<nat>, rows: nat, cols: nat) 
    returns (flatIndices: seq<nat>)
    // Input arrays must have the same length
    requires |rowIndices| == |colIndices|
    // Dimensions must be positive
    requires rows > 0 && cols > 0
    // All row indices must be within bounds
    requires forall i :: 0 <= i < |rowIndices| ==> rowIndices[i] < rows
    // All column indices must be within bounds  
    requires forall i :: 0 <= i < |colIndices| ==> colIndices[i] < cols
    // Output has same length as inputs
    ensures |flatIndices| == |rowIndices|
    // Each flat index is computed using row-major ordering formula
    ensures forall i :: 0 <= i < |flatIndices| ==> 
        flatIndices[i] == rowIndices[i] * cols + colIndices[i]
    // All flat indices are within bounds of the flattened array
    ensures forall i :: 0 <= i < |flatIndices| ==> flatIndices[i] < rows * cols
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): build flatIndices by appending in loop to avoid seq comprehension parse issue */
  var n := |rowIndices|;
  flatIndices := [];
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant |flatIndices| == k
    invariant forall j :: 0 <= j < k ==> flatIndices[j] == rowIndices[j] * cols + colIndices[j]
    invariant forall j :: 0 <= j < k ==> flatIndices[j] < rows * cols
  {
    var v := rowIndices[k] * cols + colIndices[k];
    MulAddLessThan(rows, cols, rowIndices[k], colIndices[k]);
    assert v < rows * cols;
    flatIndices := flatIndices + [v];
    k := k + 1;
  }
}

// </vc-code>
