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
lemma CountPairsLemma(A: array<int>, i: int, j: int)
  requires ValidInput(A)
  requires 0 <= i < A.Length
  requires 0 <= j < A.Length
  ensures ValidPair(A, i, j) <==> (i != j && abs(i - j) == A[i] + A[j])
{
  // The definition of ValidPair uses (i+1) and (j+1) in the positions,
  // but abs((i+1) - (j+1)) = abs(i - j)
  // This lemma helps connect the mathematical definition with the simplified version
}

lemma ValidPairSymmetric(A: array<int>, i: int, j: int)
  requires ValidInput(A)
  requires 0 <= i < A.Length && 0 <= j < A.Length
  ensures ValidPair(A, i, j) <==> ValidPair(A, j, i)
{
}

lemma SetCardinalityEquality<S(==)>(s: set<S>, t: set<S>)
  ensures s == t ==> |s| == |t|
{
}

lemma SetAdditionLemma(A: array<int>, i: int, j1: int, j2: int)
  requires ValidInput(A)
  requires 0 <= i < A.Length
  requires 0 <= j1 <= j2 <= A.Length
  ensures |set y | j1 <= y < j2 && ValidPair(A, i, y) :: (i, y)| == 
           |set y | j1 <= y < j2 && i != y && abs(i - y) == A[i] + A[y] :: (i, y)|
{
}
// </vc-helpers>
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
    invariant result == |set x, y | 0 <= x < i && 0 <= y < A.Length && ValidPair(A, x, y) :: (x, y)|
  {
    var j := 0;
    var current_count := 0;
    while j < A.Length
      invariant 0 <= j <= A.Length
      invariant current_count == |set y | 0 <= y < j && ValidPair(A, i, y) :: (i, y)|
      invariant result + current_count == |set x, y | 0 <= x < i && 0 <= y < A.Length && ValidPair(A, x, y) :: (x, y)| + 
                                        |set y | 0 <= y < j && ValidPair(A, i, y) :: (i, y)|
    {
      if ValidPair(A, i, j) {
        current_count := current_count + 1;
      }
      j := j + 1;
    }
    result := result + current_count;
    i := i + 1;
  }
}
// </vc-code>

