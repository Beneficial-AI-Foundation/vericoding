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
lemma ValidPairEquivalence(A: array<int>, i: int, j: int)
  requires ValidInput(A)
  requires 0 <= i < A.Length && 0 <= j < A.Length
  ensures ValidPair(A, i, j) <==> (i != j && abs(i - j) == A[i] + A[j])
{
  // ValidPair uses abs((i+1) - (j+1)) which equals abs(i - j)
  assert abs((i+1) - (j+1)) == abs(i - j);
}

lemma CountValidPairsCorrect(A: array<int>, pairSet: set<(int, int)>)
  requires ValidInput(A)
  requires pairSet == set x, y | 0 <= x < A.Length && 0 <= y < A.Length && ValidPair(A, x, y) :: (x, y)
  ensures |pairSet| == CountValidPairs(A)
{
  var s1 := set x, y | 0 <= x < A.Length && 0 <= y < A.Length && ValidPair(A, x, y) :: (x, y);
  assert pairSet == s1;
  assert |pairSet| == |s1|;
  assert |s1| == CountValidPairs(A);
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
  var pairSet: set<(int, int)> := {};
  
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
      if i != j {
        ValidPairEquivalence(A, i, j);
        // Check if ValidPair condition holds
        if abs(i - j) == A[i] + A[j] {
          assert ValidPair(A, i, j);
          var oldSize := |pairSet|;
          pairSet := pairSet + {(i, j)};
          if |pairSet| > oldSize {
            count := count + 1;
          }
        }
      }
    }
  }
  
  assert pairSet == set x, y | 0 <= x < A.Length && 0 <= y < A.Length && ValidPair(A, x, y) :: (x, y);
  CountValidPairsCorrect(A, pairSet);
  assert count == |pairSet|;
  assert count == CountValidPairs(A);
  return count;
}
// </vc-code>

