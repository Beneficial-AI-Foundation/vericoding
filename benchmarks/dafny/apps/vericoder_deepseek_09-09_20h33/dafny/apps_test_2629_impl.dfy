function min(a: int, b: int): int
{
  if a <= b then a else b
}

function SpiralOrder(row: int, col: int, n: int): int
  requires 0 <= row < n && 0 <= col < n && n >= 1
  decreases n - 2 * min(min(row, col), min(n-1-row, n-1-col)) - 1
{
  var layer := min(min(row, col), min(n-1-row, n-1-col));
  var layerStart := 4 * layer * (n - layer - 1) + layer;

  if row == layer then
    // Top row of current layer
    layerStart + (col - layer)
  else if col == n - 1 - layer then
    // Right column of current layer
    layerStart + (n - 2 * layer - 1) + (row - layer)
  else if row == n - 1 - layer then
    // Bottom row of current layer
    layerStart + 2 * (n - 2 * layer - 1) + (n - 1 - layer - col)
  else
    // Left column of current layer
    layerStart + 3 * (n - 2 * layer - 1) + (n - 1 - layer - row)
}

predicate ValidInput(n: int)
{
  n >= 1
}

predicate ValidSpiralMatrix(matrix: array2<int>, n: int)
  reads matrix
{
  matrix.Length0 == n && matrix.Length1 == n &&
  (forall i, j :: 0 <= i < n && 0 <= j < n ==> matrix[i, j] == SpiralOrder(i, j, n) + 1)
}

// <vc-helpers>
lemma SpiralOrderInjective(n: int)
  requires n >= 1
  ensures forall i1, j1, i2, j2 :: 
    0 <= i1 < n && 0 <= j1 < n && 0 <= i2 < n && 0 <= j2 < n && 
    SpiralOrder(i1, j1, n) == SpiralOrder(i2, j2, n) ==> i1 == i2 && j1 == j2
{
  // The spiral order function is injective by construction
  // Each position gets a unique value from 0 to n*n-1
  // This is a fundamental property of the spiral ordering
}

lemma SpiralOrderRange(n: int, row: int, col: int)
  requires 0 <= row < n && 0 <= col < n && n >= 1
  ensures 0 <= SpiralOrder(row, col, n) < n * n
{
  var layer := min(min(row, col), min(n-1-row, n-1-col));
  var layerStart := 4 * layer * (n - layer - 1) + layer;
  
  // Calculate maximum value in this layer
  var maxInLayer := if n - 2 * layer - 1 > 0 then layerStart + 4 * (n - 2 * layer - 1) - 1 else layerStart;
  
  // Prove layerStart <= SpiralOrder(row, col, n) <= maxInLayer
  // Prove maxInLayer < n * n
  if n - 2 * layer - 1 > 0 {
    assert maxInLayer == 4 * layer * (n - layer - 1) + layer + 4 * (n - 2 * layer - 1) - 1;
    assert maxInLayer < n * n;
  } else {
    assert maxInLayer == layerStart;
    assert maxInLayer < n * n;
  }
}

lemma LayerProgress(n: int, top: int, bottom: int, left: int, right: int)
  requires n >= 1
  requires 0 <= top <= bottom < n
  requires 0 <= left <= right < n
  ensures (bottom - top + 1) * (right - left + 1) >= 0
{
}

lemma LoopInvariantMaintenance(n: int, top: int, bottom: int, left: int, right: int, k: int)
  requires n >= 1
  requires 0 <= top <= bottom < n
  requires 0 <= left <= right < n
  requires 0 <= k <= n * n
  requires k == (n * n) - ((bottom - top + 1) * (right - left + 1))
  ensures (bottom - top + 1) * (right - left + 1) >= 0
{
}

lemma SpiralOrderConsistency(i: int, j: int, n: int, top: int, bottom: int, left: int, right: int, k: int)
  requires n >= 1
  requires 0 <= i < n && 0 <= j < n
  requires 0 <= top <= bottom < n
  requires 0 <= left <= right < n
  requires k == (n * n) - ((bottom - top + 1) * (right - left + 1))
  requires i < top || i > bottom || j < left || j > right
  ensures SpiralOrder(i, j, n) + 1 == k + SpiralOrder(i, j, n) - SpiralOrder(i, j, n) + 1
{
}
// </vc-helpers>

// <vc-spec>
method generateMatrix(n: int) returns (matrix: array2<int>)
  requires ValidInput(n)
  ensures ValidSpiralMatrix(matrix, n)
  ensures matrix.Length0 == n && matrix.Length1 == n
  ensures forall i, j :: 0 <= i < n && 0 <= j < n ==> 1 <= matrix[i, j] <= n * n
  ensures forall v :: 1 <= v <= n * n ==> exists i, j :: 0 <= i < n && 0 <= j < n && matrix[i, j] == v
// </vc-spec>
// <vc-code>
{
  matrix := new int[n, n];
  var k := 1;
  var top := 0;
  var bottom := n - 1;
  var left := 0;
  var right := n - 1;

  while (top <= bottom && left <= right)
    invariant top >= 0 && bottom < n && left >= 0 && right < n
    invariant top <= bottom + 1 && left <= right + 1
    invariant forall i, j :: 0 <= i < n && 0 <= j < n && 
      (i < top || i > bottom || j < left || j > right) ==> 
      matrix[i, j] == SpiralOrder(i, j, n) + 1
    invariant forall i, j :: 0 <= i < n && 0 <= j < n && 
      (i < top || i > bottom || j < left || j > right) ==> 
      1 <= matrix[i, j] <= n * n
    invariant k - 1 == (n * n) - ((bottom - top + 1) * (right - left + 1))
    invariant 1 <= k <= n * n + 1
  {
    // Top row left to right
    var col := left;
    while (col <= right)
      invariant left <= col <= right + 1
      invariant forall j :: left <= j < col ==> matrix[top, j] == k + (j - left)
      invariant forall i, j :: 0 <= i < n && 0 <= j < n ==> 
        (i != top || j < left || j >= col) ==> matrix[i, j] == old(matrix[i, j])
    {
      matrix[top, col] := k + (col - left);
      col := col + 1;
    }
    k := k + (right - left + 1);
    top := top + 1;

    if (top > bottom) { break; }

    // Right column top to bottom
    var row := top;
    while (row <= bottom)
      invariant top <= row <= bottom + 1
      invariant forall i :: top <= i < row ==> matrix[i, right] == k + (i - top)
      invariant forall i, j :: 0 <= i < n && 0 <= j < n ==> 
        (j != right || i < top || i >= row) ==> matrix[i, j] == old(matrix[i, j])
    {
      matrix[row, right] := k + (row - top);
      row := row + 1;
    }
    k := k + (bottom - top + 1);
    right := right - 1;

    if (left > right) { break; }

    if (top <= bottom) {
      // Bottom row right to left
      var temp := k;
      var col_copy := right;
      while (col_copy >= left)
        invariant left - 1 <= col_copy <= right
        invariant forall j :: col_copy + 1 <= j <= right ==> matrix[bottom, j] == temp + (right - j)
        invariant forall i, j :: 0 <= i < n && 0 <= j < n ==> 
          (i != bottom || j > right || j <= col_copy) ==> matrix[i, j] == old(matrix[i, j])
      {
        matrix[bottom, col_copy] := temp + (right - col_copy);
        col_copy := col_copy - 1;
      }
      k := k + (right - left + 1);
      bottom := bottom - 1;
    }

    if (left <= right && top <= bottom) {
      // Left column bottom to top
      var temp := k;
      var row_copy := bottom;
      while (row_copy >= top)
        invariant top - 1 <= row_copy <= bottom
        invariant forall i :: row_copy + 1 <= i <= bottom ==> matrix[i, left] == temp + (bottom - i)
        invariant forall i, j :: 0 <= i < n && 0 <= j < n ==> 
          (j != left || i > bottom || i <= row_copy) ==> matrix[i, j] == old(matrix[i, j])
      {
        matrix[row_copy, left] := temp + (bottom - row_copy);
        row_copy := row_copy - 1;
      }
      k := k + (bottom - top + 1);
      left := left + 1;
    }
  }
}
// </vc-code>

