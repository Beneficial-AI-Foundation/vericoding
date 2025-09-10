predicate ValidInput(A: array<int>)
  reads A
{
  A.Length >= 2 && forall i :: 0 <= i < A.Length ==> A[i] >= 1
}

function abs(x: int): int
{
  if x >= 0 then x else -x
}

predicate ValidPair(A: array<int>, i: int, j: int)
  reads A
  requires 0 <= i < A.Length && 0 <= j < A.Length
{
  i != j && abs((i+1) - (j+1)) == A[i] + A[j]
}

function CountValidPairs(A: array<int>): int
  reads A
  requires ValidInput(A)
{
  |set i, j | 0 <= i < A.Length && 0 <= j < A.Length && ValidPair(A, i, j) :: (i, j)|
}

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method solve(A: array<int>) returns (result: int)
  requires ValidInput(A)
  ensures result >= 0
  ensures result == CountValidPairs(A)
// </vc-spec>
// <vc-code>
{
  var n := A.Length;
  var i := 0;
  result := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result == |set p,q | 0 <= p < i && 0 <= q < n && ValidPair(A, p, q) :: (p,q)|
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant 0 <= i < n
      invariant result == |set p,q | 0 <= p < i && 0 <= q < n && ValidPair(A, p, q) :: (p,q)| + |set q | 0 <= q < j && ValidPair(A, i, q) :: (i,q)|
    {
      if i != j && abs((i+1) - (j+1)) == A[i] + A[j] {
        result := result + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

