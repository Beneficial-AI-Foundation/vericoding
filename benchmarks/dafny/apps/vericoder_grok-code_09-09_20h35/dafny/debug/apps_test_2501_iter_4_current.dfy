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
//
// </vc-helpers>

// <vc-spec>
method solve(A: array<int>) returns (result: int)
  requires ValidInput(A)
  ensures result >= 0
  ensures result == CountValidPairs(A)
// </vc-spec>
// <vc-code>
var count := 0;
    var i := 0;
    while i < A.Length
        invariant 0 <= i <= A.Length
        invariant count == |set i', j | 0 <= i' < i && 0 <= j < A.Length && i' != j && abs((i'+1) - (j+1)) == A[i'] + A[j] :: (i', j)|
    {
        var j := 0;
        while j < A.Length
            invariant 0 <= j <= A.Length
            invariant count == |set i', j' | 0 <= i' < i && 0 <= j' < A.Length && i' != j' && abs((i'+1) - (j'+1)) == A[i'] + A[j'] :: (i', j')| +
                               |set j' | 0 <= j' < j && i != j' && abs((i+1) - (j'+1)) == A[i] + A[j'] :: j'|
        {
            if i != j && abs((i + 1) - (j + 1)) == A[i] + A[j]
            {
                count := count + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    result := count;
// </vc-code>

