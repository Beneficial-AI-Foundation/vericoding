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
lemma ValidPairSymmetric(A: array<int>, i: int, j: int)
  requires 0 <= i < A.Length && 0 <= j < A.Length
  ensures ValidPair(A, i, j) <==> ValidPair(A, j, i)
{
  if ValidPair(A, i, j) {
    assert i != j;
    assert abs((i+1) - (j+1)) == A[i] + A[j];
    assert j != i;
    assert abs((j+1) - (i+1)) == abs(-((i+1) - (j+1))) == abs((i+1) - (j+1)) == A[i] + A[j] == A[j] + A[i];
  }
  if ValidPair(A, j, i) {
    assert j != i;
    assert abs((j+1) - (i+1)) == A[j] + A[i];
    assert i != j;
    assert abs((i+1) - (j+1)) == abs(-((j+1) - (i+1))) == abs((j+1) - (i+1)) == A[j] + A[i] == A[i] + A[j];
  }
}

lemma SetSizePreservation(A: array<int>, i: int, j: int)
  requires ValidInput(A)
  requires 0 <= i < A.Length && 0 <= j <= A.Length
  ensures |set p, q | 0 <= p < i && 0 <= q < A.Length && ValidPair(A, p, q) :: (p, q)| + |set q | 0 <= q < j && ValidPair(A, i, q) :: (i, q)| == |set p, q | 0 <= p <= i && 0 <= q < A.Length && ((p < i && ValidPair(A, p, q)) || (p == i && q < j && ValidPair(A, p, q))) :: (p, q)|
{
  var set1 := set p, q | 0 <= p < i && 0 <= q < A.Length && ValidPair(A, p, q) :: (p, q);
  var set2 := set q | 0 <= q < j && ValidPair(A, i, q) :: (i, q);
  var set3 := set p, q | 0 <= p <= i && 0 <= q < A.Length && ((p < i && ValidPair(A, p, q)) || (p == i && q < j && ValidPair(A, p, q))) :: (p, q);
  
  assert set1 !! set2;
  assert set3 == set1 + set2;
}

lemma LoopInvariantMaintained(A: array<int>, i: int, j: int, result: int)
  requires ValidInput(A)
  requires 0 <= i < A.Length && 0 <= j < A.Length
  requires result == |set p, q | 0 <= p < i && 0 <= q < A.Length && ValidPair(A, p, q) :: (p, q)| + |set q | 0 <= q < j && ValidPair(A, i, q) :: (i, q)|
  ensures (result + (if ValidPair(A, i, j) then 1 else 0)) == |set p, q | 0 <= p < i && 0 <= q < A.Length && ValidPair(A, p, q) :: (p, q)| + |set q | 0 <= q < j+1 && ValidPair(A, i, q) :: (i, q)|
{
  var set1 := set p, q | 0 <= p < i && 0 <= q < A.Length && ValidPair(A, p, q) :: (p, q);
  var set2_old := set q | 0 <= q < j && ValidPair(A, i, q) :: (i, q);
  var set2_new := set q | 0 <= q < j+1 && ValidPair(A, i, q) :: (i, q);
  
  if ValidPair(A, i, j) {
    assert (i, j) in set2_new && (i, j) !in set2_old;
    assert set2_new == set2_old + {(i, j)};
    assert |set2_new| == |set2_old| + 1;
  } else {
    assert set2_new == set2_old;
    assert |set2_new| == |set2_old|;
  }
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
  result := 0;
  var i := 0;
  
  while i < A.Length
    invariant 0 <= i <= A.Length
    invariant result >= 0
    invariant result == |set p, q | 0 <= p < i && 0 <= q < A.Length && ValidPair(A, p, q) :: (p, q)|
  {
    var j := 0;
    while j < A.Length
      invariant 0 <= j <= A.Length
      invariant result >= 0
      invariant result == |set p, q | 0 <= p < i && 0 <= q < A.Length && ValidPair(A, p, q) :: (p, q)| + |set q | 0 <= q < j && ValidPair(A, i, q) :: (i, q)|
    {
      if i != j && abs((i+1) - (j+1)) == A[i] + A[j] {
        LoopInvariantMaintained(A, i, j, result);
        result := result + 1;
      } else {
        LoopInvariantMaintained(A, i, j, result);
      }
      j := j + 1;
    }
    SetSizePreservation(A, i, A.Length);
    i := i + 1;
  }
  
  assert result == |set p, q | 0 <= p < A.Length && 0 <= q < A.Length && ValidPair(A, p, q) :: (p, q)|;
}
// </vc-code>

