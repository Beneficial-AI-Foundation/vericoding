// <vc-helpers>
method CreateMinor(X: array2<int>, M: int, row: int, col: int) returns (minor: array2<int>)
  requires 1 <= M
  requires X != null && M == X.Length0 && M == X.Length1
  requires 0 <= row < M && 0 <= col < M
  ensures minor != null
  ensures minor.Length0 == M - 1 && minor.Length1 == M - 1
{
  if M == 1 {
    minor := new int[0, 0];
    return;
  }
  
  minor := new int[M - 1, M - 1];
  var minorRow := 0;
  var i := 0;
  
  while i < M
    invariant 0 <= i <= M
    invariant 0 <= minorRow <= M - 1
    invariant minorRow == i - (if i > row then 1 else 0)
  {
    if i != row {
      var minorCol := 0;
      var j := 0;
      
      while j < M
        invariant 0 <= j <= M
        invariant 0 <= minorCol <= M - 1
        invariant minorCol == j - (if j > col then 1 else 0)
        invariant minorRow < M - 1
      {
        if j != col {
          minor[minorRow, minorCol] := X[i, j];
          minorCol := minorCol + 1;
        }
        j := j + 1;
      }
      minorRow := minorRow + 1;
    }
    i := i + 1;
  }
}

function Power(base: int, exp: nat): int
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}
// </vc-helpers>

// <vc-spec>
method Determinant(X: array2<int>, M: int) returns (z: int)
  requires 1 <= M
  requires X != null && M == X.Length0 && M == X.Length1
// </vc-spec>
// <vc-code>
{
  if M == 1 {
    z := X[0, 0];
    return;
  }
  
  z := 0;
  var j := 0;
  
  while j < M
    invariant 0 <= j <= M
  {
    var minor := CreateMinor(X, M, 0, j);
    var minorDet := Determinant(minor, M - 1);
    var sign := Power(-1, j);
    z := z + sign * X[0, j] * minorDet;
    j := j + 1;
  }
}
// </vc-code>