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
lemma SpiralOrderBounds(row: int, col: int, n: int)
  requires 0 <= row < n && 0 <= col < n && n >= 1
  ensures 0 <= SpiralOrder(row, col, n) < n * n
{
  var layer := min(min(row, col), min(n-1-row, n-1-col));
  var layerStart := 4 * layer * (n - layer - 1) + layer;
  
  assert 0 <= layer < n;
  assert layerStart >= 0;
  
  var layerSize := n - 2 * layer;
  assert layerSize > 0;
  
  if layer == 0 {
    assert layerStart == 0;
  }
  
  var perimeter := 4 * (layerSize - 1);
  if layerSize == 1 {
    assert perimeter == 0;
  } else {
    assert perimeter > 0;
  }
}

lemma SpiralOrderInjective(n: int)
  requires n >= 1
  ensures forall i1, j1, i2, j2 :: 
    0 <= i1 < n && 0 <= j1 < n && 0 <= i2 < n && 0 <= j2 < n &&
    (i1 != i2 || j1 != j2) ==> SpiralOrder(i1, j1, n) != SpiralOrder(i2, j2, n)
{
  forall i1, j1, i2, j2 | 0 <= i1 < n && 0 <= j1 < n && 0 <= i2 < n && 0 <= j2 < n && (i1 != i2 || j1 != j2)
    ensures SpiralOrder(i1, j1, n) != SpiralOrder(i2, j2, n)
  {
    SpiralOrderBounds(i1, j1, n);
    SpiralOrderBounds(i2, j2, n);
  }
}

lemma SpiralOrderSurjective(n: int)
  requires n >= 1
  ensures forall v :: 0 <= v < n * n ==> exists i, j :: 0 <= i < n && 0 <= j < n && SpiralOrder(i, j, n) == v
{
  forall v | 0 <= v < n * n
    ensures exists i, j :: 0 <= i < n && 0 <= j < n && SpiralOrder(i, j, n) == v
  {
    var found := false;
    for i := 0 to n
      invariant forall i' :: 0 <= i' < i ==> forall j :: 0 <= j < n ==> SpiralOrder(i', j, n) != v || found
    {
      for j := 0 to n
        invariant forall j' :: 0 <= j' < j ==> SpiralOrder(i, j', n) != v || found
      {
        SpiralOrderBounds(i, j, n);
        if SpiralOrder(i, j, n) == v {
          found := true;
          return;
        }
      }
    }
  }
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
  
  for i := 0 to n
    invariant forall i', j' :: 0 <= i' < i && 0 <= j' < n ==> matrix[i', j'] == SpiralOrder(i', j', n) + 1
  {
    for j := 0 to n
      invariant forall i', j' :: 0 <= i' < i && 0 <= j' < n ==> matrix[i', j'] == SpiralOrder(i', j', n) + 1
      invariant forall j' :: 0 <= j' < j ==> matrix[i, j'] == SpiralOrder(i, j', n) + 1
    {
      SpiralOrderBounds(i, j, n);
      matrix[i, j] := SpiralOrder(i, j, n) + 1;
    }
  }
  
  SpiralOrderInjective(n);
  SpiralOrderSurjective(n);
}
// </vc-code>

