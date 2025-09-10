predicate ValidMatrix(matrix: seq<seq<string>>)
{
    (forall i :: 0 <= i < |matrix| ==> |matrix[i]| == (if |matrix| == 0 then 0 else |matrix[0]|)) &&
    (forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| ==> matrix[i][j] == "0" || matrix[i][j] == "1")
}

function MaxPossibleArea(matrix: seq<seq<string>>): int
{
    |matrix| * (if |matrix| == 0 then 0 else |matrix[0]|)
}

predicate EmptyMatrix(matrix: seq<seq<string>>)
{
    |matrix| == 0 || |matrix[0]| == 0
}

// <vc-helpers>
predicate AllOnes(matrix: seq<seq<string>>, r1: int, r2: int, c1: int, c2: int)
  requires 0 <= r1 <= r2 < |matrix|
  requires 0 <= c1 <= c2 < |matrix[0]|
{
  forall i, j :: r1 <= i <= r2 && c1 <= j <= c2 ==> matrix[i][j] == "1"
}
// </vc-helpers>

// <vc-spec>
method maximalRectangle(matrix: seq<seq<string>>) returns (result: int)
    requires ValidMatrix(matrix)
    ensures result >= 0
    ensures EmptyMatrix(matrix) ==> result == 0
    ensures result <= MaxPossibleArea(matrix)
// </vc-spec>
// <vc-code>
{
  var m := |matrix|;
  var n := if m == 0 then 0 else |matrix[0]|;
  result := 0;
  if m == 0 || n == 0 {
    return;
  }

  // iterate over all possible rectangles [r1..r2] x [c1..c2] (inclusive)
  for r1 := 0 to m - 1
    invariant 0 <= r1 && r1 <= m
    invariant result >= 0 && result <= m * n
  {
    for c1 := 0 to n - 1
      invariant 0 <= c1 && c1 <= n
      invariant result >= 0 && result <= m * n
    {
      for r2 := r1 to m - 1
        invariant r1 <= r2 && r2 < m
        invariant result >= 0 && result <= m * n
      {
        for c2 := c1 to n - 1
          invariant c1 <= c2 && c2 < n
          invariant result >= 0 && result <= m * n
        {
          if AllOnes(matrix, r1, r2, c1, c2) {
            var area := (r2 - r1 + 1) * (c2 - c1 + 1);
            // prove area does not exceed m*n to preserve the invariant
            assert (r2 - r1 + 1) <= m;
            assert (c2 - c1 + 1) <= n;
            assert area <= m * n;
            if area > result {
              result := area;
            }
          }
        }
      }
    }
  }

  // Final checks to match ensures
  assert result >= 0;
  assert result <= m * n;
  assert MaxPossibleArea(matrix) == m * n;
  assert result <= MaxPossibleArea(matrix);
}
// </vc-code>

