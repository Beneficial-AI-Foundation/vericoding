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
function min(a: int, b: int): int
{
  if a <= b then a else b
}

function SpiralOrder(row: int, col: int, n: int): int
  requires 0 <= row < n && 0 <= col < n && n >= 1
  decreases 2 * n - 1 - (min(min(row, col), min(n-1-row, n-1-col)) * 2) // this termination metric is important
{
  var layer := min(min(row, col), min(n-1-row, n-1-col));
  var layerStart := 0;
  if layer > 0
  {
      layerStart := 4 * (layer - 1) * (n - (layer - 1) - 1) + (layer - 1);
      layerStart := layerStart + 4 * (n - 2 * (layer -1) - 1); // Corrected calculation
  }

  var currentLayerSize := n - 2 * layer;

  if row == layer then
    // Top row of current layer
    layerStart + (col - layer) + 1
  else if col == n - 1 - layer then
    // Right column of current layer
    layerStart + (currentLayerSize - 1) + (row - layer) + 1
  else if row == n - 1 - layer then
    // Bottom row of current layer
    layerStart + 2 * (currentLayerSize - 1) + (n - 1 - layer - col) + 1
  else
    // Left column of current layer
    layerStart + 3 * (currentLayerSize - 1) + (n - 1 - layer - row) + 1
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
  var matrix := new array2<int>(n, n);

  if n == 0 {
    return matrix;
  }

  var value := 1;
  var layer := 0;

  while layer * 2 < n
    invariant 0 <= layer * 2 <= n
    invariant forall i, j :: 0 <= i < n && 0 <= j < n && (min(min(i, j), min(n-1-i, n-1-j)) < layer) ==> matrix[i,j] == SpiralOrder(i,j,n)
    invariant forall i, j :: 0 <= i < n && 0 <= j < n && (min(min(i, j), min(n-1-i, n-1-j)) < layer) ==> 1 <= matrix[i,j] <= n * n
    invariant forall p, q :: 0 <= p < n && 0 <= q < n && (min(min(p, q), min(n-1-p, n-1-q)) >= layer && SpiralOrder(p,q,n) < value) ==> matrix[p,q] == SpiralOrder(p,q,n)
    invariant forall p, q :: 0 <= p < n && 0 <= q < n && SpiralOrder(p,q,n) < value ==> 1 <= matrix[p,q] <= n*n
  {
    var currentLayerSize := n - 2 * layer;
    if currentLayerSize == 0 {
        break;
    }

    // Fill top row
    var j := layer;
    while j < n - layer
      invariant layer <= j <= n - layer
      invariant forall k :: layer <= k < j ==> matrix[layer, k] == SpiralOrder(layer, k, n)
      invariant forall i, k :: 0 <= i < n && 0 <= k < n && (min(min(i, k), min(n-1-i, n-1-k)) < layer) ==> matrix[i,k] == SpiralOrder(i,k,n)
      invariant forall p, q :: 0 <= p < n && 0 <= q < n && (min(min(p, q), min(n-1-p, n-1-q)) >= layer && SpiralOrder(p,q,n) < value) ==> matrix[p,q] == SpiralOrder(p,q,n)
      decreases n - layer - j
    {
      matrix[layer, j] := value;
      value := value + 1;
      j := j + 1;
    }

    // Fill right column
    var i := layer + 1;
    while i < n - layer
      invariant layer + 1 <= i <= n - layer
      invariant forall k :: layer <= k < n - layer ==> matrix[layer, k] == SpiralOrder(layer, k, n)
      invariant forall k :: layer + 1 <= k < i ==> matrix[k, n - 1 - layer] == SpiralOrder(k, n - 1 - layer, n)
      invariant forall r, c :: 0 <= r < n && 0 <= c < n && (min(min(r, c), min(n-1-r, n-1-c)) < layer) ==> matrix[r,c] == SpiralOrder(r,c,n)
      invariant forall p, q :: 0 <= p < n && 0 <= q < n && (min(min(p, q), min(n-1-p, n-1-q)) >= layer && SpiralOrder(p,q,n) < value) ==> matrix[p,q] == SpiralOrder(p,q,n)
      decreases n - layer - i
    {
      matrix[i, n - 1 - layer] := value;
      value := value + 1;
      i := i + 1;
    }

    if currentLayerSize > 1 {
      // Fill bottom row
      j := n - 2 - layer;
      while j >= layer
        invariant layer - 1 <= j <= n - 2 - layer
        invariant forall k :: layer <= k < n - layer ==> matrix[layer, k] == SpiralOrder(layer, k, n)
        invariant forall k :: layer + 1 <= k < n - layer ==> matrix[k, n - 1 - layer] == SpiralOrder(k, n - 1 - layer, n)
        invariant forall k :: j < k <= n - 2 - layer ==> matrix[n - 1 - layer, k] == SpiralOrder(n - 1 - layer, k, n)
        invariant forall r, c :: 0 <= r < n && 0 <= c < n && (min(min(r, c), min(n-1-r, n-1-c)) < layer) ==> matrix[r,c] == SpiralOrder(r,c,n)
        invariant forall p, q :: 0 <= p < n && 0 <= q < n && (min(min(p, q), min(n-1-p, n-1-q)) >= layer && SpiralOrder(p,q,n) < value) ==> matrix[p,q] == SpiralOrder(p,q,n)
        decreases j - layer + 1
      {
        matrix[n - 1 - layer, j] := value;
        value := value + 1;
        j := j - 1;
      }

      // Fill left column
      i := n - 2 - layer;
      while i > layer
        invariant layer <= i <= n - 2 - layer
        invariant forall k :: layer <= k < n - layer ==> matrix[layer, k] == SpiralOrder(layer, k, n)
        invariant forall k :: layer + 1 <= k < n - layer ==> matrix[k, n - 1 - layer] == SpiralOrder(k, n - 1 - layer, n)
        invariant forall k :: layer <= k < n - layer - 1 ==> matrix[n - 1 - layer, k] == SpiralOrder(n - 1 - layer, k, n)
        invariant forall k :: i < k <= n - 2 - layer ==> matrix[k, layer] == SpiralOrder(k, layer, n)
        invariant forall r, c :: 0 <= r < n && 0 <= c < n && (min(min(r, c), min(n-1-r, n-1-c)) < layer) ==> matrix[r,c] == SpiralOrder(r,c,n)
        invariant forall p, q :: 0 <= p < n && 0 <= q < n && (min(min(p, q), min(n-1-p, n-1-q)) >= layer && SpiralOrder(p,q,n) < value) ==> matrix[p,q] == SpiralOrder(p,q,n)
        decreases i - layer
      {
        matrix[i, layer] := value;
        value := value + 1;
        i := i - 1;
      }
    }
    layer := layer + 1;
  }

  return matrix;
}
// </vc-code>

