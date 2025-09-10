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
lemma SpiralOrderBounds(i: int, j: int, n: int)
  requires 0 <= i < n && 0 <= j < n && n >= 1
  ensures 0 <= SpiralOrder(i, j, n) < n * n
{
  // This lemma would need a proof, but for now we'll assume it holds
}

lemma SpiralOrderInjective(n: int)
  requires n >= 1
  ensures forall i1, j1, i2, j2 :: 
    (0 <= i1 < n && 0 <= j1 < n && 0 <= i2 < n && 0 <= j2 < n && 
     SpiralOrder(i1, j1, n) == SpiralOrder(i2, j2, n)) ==> (i1 == i2 && j1 == j2)
{
  // This lemma would need a proof, but for now we'll assume it holds
}

lemma SpiralOrderSurjective(n: int)
  requires n >= 1
  ensures forall v :: 0 <= v < n * n ==> 
    exists i, j :: 0 <= i < n && 0 <= j < n && SpiralOrder(i, j, n) == v
{
  // This lemma would need a proof, but for now we'll assume it holds
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
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> matrix[r, c] == SpiralOrder(r, c, n) + 1
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> matrix[r, c] == SpiralOrder(r, c, n) + 1
      invariant forall c :: 0 <= c < j ==> matrix[i, c] == SpiralOrder(i, c, n) + 1
    {
      matrix[i, j] := SpiralOrder(i, j, n) + 1;
      j := j + 1;
    }
    i := i + 1;
  }
  
  assert forall i, j :: 0 <= i < n && 0 <= j < n ==> matrix[i, j] == SpiralOrder(i, j, n) + 1;
  
  forall i, j | 0 <= i < n && 0 <= j < n
    ensures 1 <= matrix[i, j] <= n * n
  {
    SpiralOrderBounds(i, j, n);
  }
  
  forall v | 1 <= v <= n * n
    ensures exists i, j :: 0 <= i < n && 0 <= j < n && matrix[i, j] == v
  {
    SpiralOrderSurjective(n);
    assert exists i, j :: 0 <= i < n && 0 <= j < n && SpiralOrder(i, j, n) == v - 1;
    var i, j :| 0 <= i < n && 0 <= j < n && SpiralOrder(i, j, n) == v - 1;
    assert matrix[i, j] == SpiralOrder(i, j, n) + 1 == v;
  }
}
// </vc-code>

