predicate ValidInput(n: int, A: seq<int>)
{
    n >= 1 &&
    |A| == n &&
    (forall i :: 0 <= i < n ==> 0 <= A[i] < n) &&
    (forall i, j :: 0 <= i < j < n ==> A[i] != A[j]) &&
    (forall k {:trigger A[k]} :: 0 <= k < n ==> exists i :: 0 <= i < n && A[i] == k)
}

function CurrentFixedPoints(A: seq<int>): int
    requires |A| >= 0
{
    |set i | 0 <= i < |A| && A[i] == i|
}

function MaxPossibleFixedPoints(A: seq<int>): int
    requires ValidInput(|A|, A)
{
    var current := CurrentFixedPoints(A);
    if current == |A| then 
        |A|
    else if exists i :: 0 <= i < |A| && A[i] != i && A[A[i]] == i then
        current + 2
    else
        current + 1
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, A: seq<int>) returns (result: int)
    requires ValidInput(n, A)
    ensures result == MaxPossibleFixedPoints(A)
    ensures result >= 0
// </vc-spec>
// <vc-code>
var current := 0;
var i := 0;
while i < n 
  invariant 0 <= i <= n
  invariant current == |set j | 0 <= j < i && A[j] == j|
{
  if A[i] == i {
    current := current + 1;
  }
  i := i + 1;
}

if current == n {
  result := n;
} else {
  var hasPair := false;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant hasPair == exists k :: 0 <= k < i && A[k] != k && A[A[k]] == k
  {
    if A[i] != i && A[A[i]] == i {
      hasPair := true;
    }
    i := i + 1;
  }
  if hasPair {
    result := current + 2;
  } else {
    result := current + 1;
  }
}
// </vc-code>

