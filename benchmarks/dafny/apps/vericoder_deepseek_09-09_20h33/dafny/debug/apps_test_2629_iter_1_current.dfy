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
}

lemma SpiralOrderRange(n: int, row: int, col: int)
  requires 0 <= row < n && 0 <= col < n && n >= 1
  ensures 0 <= SpiralOrder(row, col, n) < n * n
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
  var k := 0;
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
    invariant k == (n * n) - ((bottom - top + 1) * (right - left + 1))
    invariant 0 <= k <= n * n
  {
    // Top row left to right
    for col_copy := left to right
      invariant left <= col_copy <= right + 1
      invariant forall j :: left <= j < col_copy ==> matrix[top, j] == k + (j - left) + 1
      invariant forall i, j :: 0 <= i < n && 0 <= j < n && 
        (i < top || i > bottom || j < left || j > right || (i == top && j >= col_copy)) ==>
        matrix[i, j] == old(matrix[i, j])
      invariant k + (col_copy - left) <= n * n
    {
      matrix[top, col_copy] := k + (col_copy - left) + 1;
    }
    k := k + (right - left + 1);
    top := top + 1;

    // Right column top to bottom
    for row_copy := top to bottom
      invariant top <= row_copy <= bottom + 1
      invariant forall i :: top <= i < row_copy ==> matrix[i, right] == k + (i - top) + 1
      invariant forall i, j :: 0 <= i < n && 0 <= j < n && 
        (i < top - 1 || i > bottom || j < left || j > right || (i >= row_copy && j == right)) ==>
        matrix[i, j] == old(matrix[i, j])
      invariant k + (row_copy - top) <= n * n
    {
      matrix[row_copy, right] := k + (row_copy - top) + 1;
    }
    k := k + (bottom - top + 1);
    right := right - 1;

    if (top <= bottom) {
      // Bottom row right to left
      var temp := k;
      for col_copy := right downto left
        invariant left - 1 <= col_copy <= right
        invariant forall j :: col_copy + 1 <= j <= right ==> matrix[bottom, j] == temp + (right - j) + 1
        invariant forall i, j :: 0 <= i < n && 0 <= j < n && 
          (i < top - 1 || i > bottom || j < left || j > right + 1 || (i == bottom && j <= col_copy)) ==>
          matrix[i, j] == old(matrix[i, j])
        invariant temp + (right - col_copy) <= n * n
      {
        matrix[bottom, col_copy] := temp + (right - col_copy) + 1;
      }
      k := k + (right - left + 1);
      bottom := bottom - 1;
    }

    if (left <= right) {
      // Left column bottom to top
      var temp := k;
      for row_copy := bottom downto top
        invariant top - 1 <= row_copy <= bottom
        invariant forall i :: row_copy + 1 <= i <= bottom ==> matrix[i, left] == temp + (bottom - i) + 1
        invariant forall i, j :: 0 <= i < n && 0 <= j < n && 
          (i < top - 1 || i > bottom + 1 || j < left || j > right + 1 || (i <= row_copy && j == left)) ==>
          matrix[i, j] == old(matrix[i, j])
        invariant temp + (bottom - row_copy) <= n * n
      {
        matrix[row_copy, left] := temp + (bottom - row_copy) + 1;
      }
      k := k + (bottom - top + 1);
      left := left + 1;
    }
  }
}
// </vc-code>

