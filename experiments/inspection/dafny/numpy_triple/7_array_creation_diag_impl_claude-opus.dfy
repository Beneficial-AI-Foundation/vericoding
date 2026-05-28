// <vc-preamble>
/*
 * Diagonal matrix construction from 1-D vector.
 * 
 * This module provides functionality to construct a square diagonal matrix
 * from a 1-D vector, where the input vector elements are placed on the main
 * diagonal and all off-diagonal elements are zero.
 */
// </vc-preamble>

// <vc-helpers>
function createRow(v: seq<real>, rowIndex: int, colIndex: int): real
  requires 0 <= rowIndex < |v|
  requires 0 <= colIndex < |v|
{
  if rowIndex == colIndex then v[rowIndex] else 0.0
}

function buildRow(v: seq<real>, rowIndex: int): seq<real>
  requires 0 <= rowIndex < |v|
  ensures |buildRow(v, rowIndex)| == |v|
  ensures forall j :: 0 <= j < |v| ==> buildRow(v, rowIndex)[j] == createRow(v, rowIndex, j)
  ensures buildRow(v, rowIndex)[rowIndex] == v[rowIndex]
  ensures forall j :: 0 <= j < |v| && j != rowIndex ==> buildRow(v, rowIndex)[j] == 0.0
{
  seq(|v|, j requires 0 <= j < |v| => createRow(v, rowIndex, j))
}
// </vc-helpers>

// <vc-spec>
method diag(v: seq<real>) returns (result: seq<seq<real>>)
    requires |v| >= 0
    ensures |result| == |v|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |v|
    
    // 1. Elements on the main diagonal are from v
    ensures forall i :: 0 <= i < |v| ==> result[i][i] == v[i]
    
    // 2. All off-diagonal elements are zero  
    ensures forall i, j :: 0 <= i < |v| && 0 <= j < |v| && i != j ==> result[i][j] == 0.0
    
    // 3. Sanity check: diagonal matrix property - non-zero elements only on diagonal
    ensures forall i, j :: 0 <= i < |v| && 0 <= j < |v| && result[i][j] != 0.0 ==> i == j
    
    // 4. Matrix trace equals sum of input vector elements
    // ensures (sum i | 0 <= i < |v| :: result[i][i]) == (sum i | 0 <= i < |v| :: v[i])
    
    // 5. The resulting matrix is symmetric
    ensures forall i, j :: 0 <= i < |v| && 0 <= j < |v| ==> result[i][j] == result[j][i]
    
    // 6. Row and column sums: for each row/column, sum equals the corresponding diagonal element
    // ensures forall i :: 0 <= i < |v| ==> 
    //     (sum j | 0 <= j < |v| :: result[i][j]) == v[i]
    // ensures forall j :: 0 <= j < |v| ==> 
    //     (sum i | 0 <= i < |v| :: result[i][j]) == v[j]
        
    // 7. Each row has exactly one non-zero element at position i (unless v[i] = 0)
    ensures forall i :: 0 <= i < |v| && v[i] != 0.0 ==> 
        result[i][i] != 0.0 && (forall j :: 0 <= j < |v| && j != i ==> result[i][j] == 0.0)
    
    // 8. Each column has exactly one non-zero element at position j (unless v[j] = 0)
    ensures forall j :: 0 <= j < |v| && v[j] != 0.0 ==> 
        result[j][j] != 0.0 && (forall i :: 0 <= i < |v| && i != j ==> result[i][j] == 0.0)
// </vc-spec>
// <vc-code>
{
  result := seq(|v|, i requires 0 <= i < |v| => buildRow(v, i));
}
// </vc-code>
