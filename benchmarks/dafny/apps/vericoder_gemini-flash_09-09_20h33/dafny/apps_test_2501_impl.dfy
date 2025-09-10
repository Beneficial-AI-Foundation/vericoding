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
predicate PairExists(A: array<int>, i: int, j: int)
  reads A
  requires 0 <= i < A.Length && 0 <= j < A.Length
{
  ValidPair(A, i, j)
}

// Helper predicate to define the set of pairs counted by the outer loop
predicate CountedPairsBeforeI(A: array<int>, limit_i: int, p: int, q: int)
  reads A
  requires 0 <= limit_i <= A.Length
{
  0 <= p < limit_i && p < q && 0 <= q < A.Length && ValidPair(A, p, q)
}

// Helper predicate to define the set of pairs counted by the inner loop
predicate CountedPairsForI(A: array<int>, current_i: int, limit_j: int, p: int, q: int)
  reads A
  requires 0 <= current_i < A.Length && current_i <= limit_j <= A.Length
{
  p == current_i && current_i < q && q < limit_j && ValidPair(A, p, q)
}
// </vc-helpers>

// <vc-spec>
method solve(A: array<int>) returns (result: int)
  requires ValidInput(A)
  ensures result >= 0
  ensures result == CountValidPairs(A)
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var n := A.Length;

  var i := 0;
  while i < n
    invariant 0 <= i <= n;
    invariant count == 2 * |set p, q | CountedPairsBeforeI(A, i, p, q) :: (p, q)|;
  {
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n;
      invariant count == (2 * |set p, q | CountedPairsBeforeI(A, i, p, q) :: (p, q)|) +
                        (2 * |set p, q | CountedPairsForI(A, i, j, p, q) :: (p, q)|);
    {
      if ValidPair(A, i, j) {
        count := count + 2; 
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  result := count;
}
// </vc-code>

