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
lemma SetComprehensionCount(A: array<int>, count: int)
  requires ValidInput(A)
  requires count >= 0
  requires count == |set i, j | 0 <= i < A.Length && 0 <= j < A.Length && i < j && abs(i - j) == A[i] + A[j] :: (i, j)| * 2
  ensures count == CountValidPairs(A)
{
  var s1 := set i, j | 0 <= i < A.Length && 0 <= j < A.Length && ValidPair(A, i, j) :: (i, j);
  var s2 := set i, j | 0 <= i < A.Length && 0 <= j < A.Length && i < j && abs(i - j) == A[i] + A[j] :: (i, j);
  
  assert forall i, j :: 0 <= i < j < A.Length && abs(i - j) == A[i] + A[j] ==> 
    (i, j) in s1 && (j, i) in s1;
  
  assert forall p :: p in s1 ==> 
    (exists i, j :: 0 <= i < A.Length && 0 <= j < A.Length && i != j && p == (i, j) && 
     abs(i - j) == A[i] + A[j]);
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
  var pairSet := {};
  
  for i := 0 to A.Length
    invariant 0 <= i <= A.Length
    invariant count >= 0
    invariant pairSet == set x, y | 0 <= x < i && 0 <= y < A.Length && ValidPair(A, x, y) :: (x, y)
    invariant count == |pairSet|
  {
    for j := 0 to A.Length
      invariant 0 <= j <= A.Length
      invariant count >= 0
      invariant pairSet == (set x, y | 0 <= x < i && 0 <= y < A.Length && ValidPair(A, x, y) :: (x, y)) +
                           (set y | 0 <= y < j && ValidPair(A, i, y) :: (i, y))
      invariant count == |pairSet|
    {
      if i != j && abs(i - j) == A[i] + A[j] {
        var oldSize := |pairSet|;
        pairSet := pairSet + {(i, j)};
        if |pairSet| > oldSize {
          count := count + 1;
        }
      }
    }
  }
  
  assert pairSet == set x, y | 0 <= x < A.Length && 0 <= y < A.Length && ValidPair(A, x, y) :: (x, y);
  return count;
}
// </vc-code>

