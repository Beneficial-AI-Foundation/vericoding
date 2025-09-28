// <vc-preamble>
// Main method that converts 2D multi-indices to flat indices
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simplified bound proof for row-major indexing */
lemma RavelBound(rows: nat, cols: nat, r: nat, c: nat)
  requires rows > 0 && cols > 0
  requires r < rows
  requires c < cols
  ensures r * cols + c < rows * cols
{
  // c < cols implies r*cols + c < r*cols + cols = (r+1)*cols
  assert r * cols + c < r * cols + cols;
  assert r * cols + cols == (r + 1) * cols;
  // r + 1 <= rows, and cols > 0, hence (r+1)*cols <= rows*cols
  assert r + 1 <= rows;
  assert (r + 1) * cols <= rows * cols;
  // combine
  assert r * cols + c < rows * cols;
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
  /* code modified by LLM (iteration 3): build result via loop, avoid comprehension parse issue, and prove bounds via helper lemma */
  var n := |rowIndices|;
  var s: seq<nat> := [];
  var i: nat := 0;
  while i < n
    invariant |s| == i
    invariant i <= n
    invariant forall j :: 0 <= j < i ==> s[j] == rowIndices[j] * cols + colIndices[j]
    invariant forall j :: 0 <= j < i ==> s[j] < rows * cols
  {
    assert rowIndices[i] < rows;
    assert colIndices[i] < cols;
    // non-negativity for nat coercion
    assert 0 <= rowIndices[i] * cols;
    assert 0 <= rowIndices[i] * cols + colIndices[i];
    var v: nat := rowIndices[i] * cols + colIndices[i];
    // bound using helper lemma
    RavelBound(rows, cols, rowIndices[i], colIndices[i]);
    assert v < rows * cols;
    s := s + [v];
    assert |s| == i + 1;
    assert s[i] == v;
    i := i + 1;
  }
  flatIndices := s;
}

// </vc-code>
