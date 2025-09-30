// <vc-preamble>
// Main method that converts 2D multi-indices to flat indices
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 3): Added assertion to help verify loop invariant */
  flatIndices := [];
  var i := 0;
  while i < |rowIndices|
    invariant 0 <= i <= |rowIndices|
    invariant |flatIndices| == i
    invariant forall j :: 0 <= j < i ==> flatIndices[j] == rowIndices[j] * cols + colIndices[j]
    invariant forall j :: 0 <= j < i ==> flatIndices[j] < rows * cols
  {
    var flatIndex := rowIndices[i] * cols + colIndices[i];
    assert rowIndices[i] < rows && colIndices[i] < cols;
    assert flatIndex == rowIndices[i] * cols + colIndices[i];
    assert rowIndices[i] * cols <= (rows - 1) * cols;
    assert flatIndex < rows * cols;
    flatIndices := flatIndices + [flatIndex];
    i := i + 1;
  }
}
// </vc-code>
