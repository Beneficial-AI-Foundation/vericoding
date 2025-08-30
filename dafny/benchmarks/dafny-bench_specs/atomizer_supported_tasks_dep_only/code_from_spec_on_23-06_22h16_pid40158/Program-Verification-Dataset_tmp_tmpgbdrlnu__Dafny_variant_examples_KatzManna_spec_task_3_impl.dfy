// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//ATOM NinetyOne
// Placeholder atom - assumed to be implemented correctly
function NinetyOne(): int { 91 }

//ATOM Gcd
// Placeholder atom - assumed to be implemented correctly  
function Gcd(a: int, b: int): int
  requires b >= 0
{
  if b == 0 then a else Gcd(b, a % b)
}

//IMPL Determinant
/* code modified by LLM (iteration 2): Added helper method to create submatrix */
method CreateSubmatrix(X: array2<int>, M: int, skipRow: int, skipCol: int, sub: array2<int>)
  requires 1 <= M
  requires X != null && M == X.Length0 && M == X.Length1
  requires 0 <= skipRow < M && 0 <= skipCol < M
  requires sub != null && (M-1) == sub.Length0 && (M-1) == sub.Length1
  requires M > 1
  modifies sub
  ensures sub != null
{
  var i := 0;
  var subI := 0;
  while i < M
    invariant 0 <= i <= M
    invariant subI == i - (if i > skipRow then 1 else 0)
    invariant 0 <= subI <= M-1
  {
    if i != skipRow {
      var j := 0;
      var subJ := 0;
      while j < M
        invariant 0 <= j <= M
        invariant subJ == j - (if j > skipCol then 1 else 0)
        invariant 0 <= subJ <= M-1
      {
        if j != skipCol {
          sub[subI, subJ] := X[i, j];
          subJ := subJ + 1;
        }
        j := j + 1;
      }
      subI := subI + 1;
    }
    i := i + 1;
  }
}

/* code modified by LLM (iteration 2): Added helper method for determinant calculation with size parameter for termination */
method DeterminantHelper(X: array2<int>, M: int) returns (z: int)
  requires 1 <= M
  requires X != null && M == X.Length0 && M == X.Length1
  modifies X
  decreases M
{
  if M == 1 {
    z := X[0, 0];
  } else if M == 2 {
    z := X[0, 0] * X[1, 1] - X[0, 1] * X[1, 0];
  } else {
    z := 0;
    var j := 0;
    while j < M
      invariant 0 <= j <= M
    {
      if X[0, j] != 0 {
        var submatrix := new int[M-1, M-1];
        CreateSubmatrix(X, M, 0, j, submatrix);
        
        /* code modified by LLM (iteration 2): Use helper method for recursion with proper termination */
        var minor := DeterminantHelper(submatrix, M-1);
        
        var cofactor := X[0, j] * minor;
        if j % 2 == 1 {
          cofactor := -cofactor;
        }
        z := z + cofactor;
      }
      j := j + 1;
    }
  }
}

method Determinant(X: array2<int>, M: int) returns (z: int)
  requires 1 <= M;
  requires X != null && M == X.Length0 && M == X.Length1;
  modifies X;
{
  /* code modified by LLM (iteration 2): Delegate to helper method for proper termination handling */
  z := DeterminantHelper(X, M);
}