// <vc-preamble>
// Main method that converts 2D multi-indices to flat indices
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed lemma body to actually prove the postcondition */
function ValidateDimensions(rows: nat, cols: nat): bool { rows > 0 && cols > 0 }
predicate IndicesInBounds(rowIndices: seq<nat>, colIndices: seq<nat>, rows: nat, cols: nat) {
  |rowIndices| == |colIndices| &&
  (forall i :: 0 <= i < |rowIndices| ==> rowIndices[i] < rows && colIndices[i] < cols)
}
lemma FlatIndexBoundsLemma(row: nat, col: nat, rows: nat, cols: nat) 
  requires rows > 0 && cols > 0 && row < rows && col < cols
  ensures row * cols + col < rows * cols
{
  var total_cells := rows * cols;
  var max_row_index := rows - 1;
  var max_col_index := cols - 1;
  var max_flat_index := max_row_index * cols + max_col_index;
  assert max_flat_index == (rows - 1) * cols + (cols - 1);
  assert max_flat_index == rows * cols - cols + cols - 1;
  assert max_flat_index == rows * cols - 1;
  assert row * cols + col <= max_flat_index;
  assert row * cols + col < total_cells;
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
/* code modified by LLM (iteration 3): Added lemma calls to prove the bounds condition */
{
  var result := new nat[|rowIndices|];
  var i: int := 0;
  while i < |rowIndices|
    invariant 0 <= i <= |rowIndices|
    invariant forall j :: 0 <= j < i ==> result[j] == rowIndices[j] * cols + colIndices[j]
    invariant forall j :: 0 <= j < i ==> result[j] < rows * cols
  {
    result[i] := rowIndices[i] * cols + colIndices[i];
    FlatIndexBoundsLemma(rowIndices[i], colIndices[i], rows, cols);
    i := i + 1;
  }
  flatIndices := result[..];
}
// </vc-code>
