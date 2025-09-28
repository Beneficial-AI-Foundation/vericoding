// <vc-preamble>
// Main method that converts 2D multi-indices to flat indices
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): helper lemma to prove flat index bounds */
lemma FlatIndexBound(rowIndex: nat, colIndex: nat, rows: nat, cols: nat)
  requires rowIndex < rows
  requires colIndex < cols
  requires rows > 0 && cols > 0
  ensures rowIndex * cols + colIndex < rows * cols
{
  assert rowIndex < rows;
  assert colIndex < cols;
  assert rowIndex * cols <= (rows - 1) * cols;
  assert (rows - 1) * cols + colIndex < (rows - 1) * cols + cols;
  assert (rows - 1) * cols + cols == rows * cols;
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
  /* code modified by LLM (iteration 2): added helper lemma call to prove bounds invariant */
  flatIndices := [];
  var i := 0;
  while i < |rowIndices|
    invariant 0 <= i <= |rowIndices|
    invariant |flatIndices| == i
    invariant forall j :: 0 <= j < i ==> flatIndices[j] == rowIndices[j] * cols + colIndices[j]
    invariant forall j :: 0 <= j < i ==> flatIndices[j] < rows * cols
  {
    FlatIndexBound(rowIndices[i], colIndices[i], rows, cols);
    var flatIndex := rowIndices[i] * cols + colIndices[i];
    flatIndices := flatIndices + [flatIndex];
    i := i + 1;
  }
}
// </vc-code>
