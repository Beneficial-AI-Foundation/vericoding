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
  
  var layerSize := if layer < n / 2 then 4 * (n - 2 * layer - 1) else 1;
  assert SpiralOrder(row, col, n) >= layerStart;
  assert SpiralOrder(row, col, n) < layerStart + layerSize;
  assert layerStart + layerSize <= n * n;
}

lemma SpiralOrderInjective(n: int)
  requires n >= 1
  ensures forall i1, j1, i2, j2 :: 
    (0 <= i1 < n && 0 <= j1 < n && 0 <= i2 < n && 0 <= j2 < n &&
    (i1 != i2 || j1 != j2)) ==> SpiralOrder(i1, j1, n) != SpiralOrder(i2, j2, n)
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
  ensures forall v {:trigger SpiralOrder(v / n, v % n, n)} :: 0 <= v < n * n ==> exists i, j :: 0 <= i < n && 0 <= j < n && SpiralOrder(i, j, n) == v
{
  forall v | 0 <= v < n * n
    ensures exists i, j :: 0 <= i < n && 0 <= j < n && SpiralOrder(i, j, n) == v
  {
    SpiralOrderComplete(n);
  }
}

lemma SpiralOrderComplete(n: int)
  requires n >= 1
  ensures forall i, j {:trigger SpiralOrder(i, j, n)} :: 0 <= i < n && 0 <= j < n ==> 0 <= SpiralOrder(i, j, n) < n * n
  ensures forall i, j {:trigger SpiralOrder(i, j, n)} :: 0 <= i < n && 0 <= j < n ==> 1 <= SpiralOrder(i, j, n) + 1 <= n * n
{
  forall i, j | 0 <= i < n && 0 <= j < n
    ensures 0 <= SpiralOrder(i, j, n) < n * n
    ensures 1 <= SpiralOrder(i, j, n) + 1 <= n * n
  {
    SpiralOrderBounds(i, j, n);
  }
}

lemma SpiralOrderBijective(n: int)
  requires n >= 1
  ensures forall v :: 0 <= v < n * n ==> exists! i, j :: 0 <= i < n && 0 <= j < n && SpiralOrder(i, j, n) == v
{
  SpiralOrderInjective(n);
  forall v | 0 <= v < n * n
    ensures exists i, j :: 0 <= i < n && 0 <= j < n && SpiralOrder(i, j, n) == v
  {
    var i := v / n;
    var j := v % n;
    if 0 <= i < n && 0 <= j < n {
      SpiralOrderBounds(i, j, n);
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
  
  SpiralOrderComplete(n);
  SpiralOrderBijective(n);
  
  forall v | 1 <= v <= n * n
    ensures exists i, j :: 0 <= i < n && 0 <= j < n && matrix[i, j] == v
  {
    assert exists i, j :: 0 <= i < n && 0 <= j < n && SpiralOrder(i, j, n) == v - 1;
    var i, j :| 0 <= i < n && 0 <= j < n && SpiralOrder(i, j, n) == v - 1;
    assert matrix[i, j] == v;
  }
}
// </vc-code>

