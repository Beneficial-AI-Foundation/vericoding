/*
Bubble Sort is the simplest sorting algorithm that works by 
repeatedly swapping the adjacent elements if they are in wrong order.
*/

predicate sorted_between(A:array<int>, from:int, to:int)
    reads A
{
    forall i, j :: 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}

predicate sorted(A:array<int>)
    reads A
{
    sorted_between(A, 0, A.Length-1)
}

/* Explanation:

invariant forall n, m :: 0 <= n <= i <m <N ==> A [n] <= A [m]
     // A is ordered for each pair of elements such that
     // the first element belongs to the left partition of i
     // and the second element belongs to the right partition of i

invariant forall n :: 0 <= n <= j ==> A [n] <= A [j]
     // There is a variable defined by the value that the array takes at position j
     // Therefore, each value that the array takes for all elements from 0 to j
     // They are less than or equal to the value of the variable
*/

// <vc-helpers>
lemma SortedBetweenImpliesSorted(A: array<int>, from: int, to: int)
  requires 0 <= from <= to < A.Length
  requires sorted_between(A, from, to)
  ensures forall i, j :: from <= i <= j <= to ==> A[i] <= A[j]
{
}

lemma SortedBetweenExtension(A: array<int>, from: int, to: int)
  requires 0 <= from <= to < A.Length
  requires sorted_between(A, from, to-1)
  requires to > 0 ==> A[to-1] <= A[to]
  ensures sorted_between(A, from, to)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method BubbleSort(A:array<int>)
    modifies A
    ensures sorted(A)
    ensures multiset(A[..]) == multiset(old(A[..]))
// </vc-spec>
// </vc-spec>

// <vc-code>
method BubbleSortImpl(A: array<int>)
  modifies A
  ensures sorted(A)
  ensures multiset(A[..]) == multiset(old(A[..]))
{
  if A.Length <= 1 {
    return;
  }

  var N := A.Length;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sorted_between(A, 0, i)
    invariant multiset(A[..]) == multiset(old(A[..]))
  {
    var j := 0;
    while j < N - 1 - i
      invariant 0 <= j < N - i
      invariant sorted_between(A, 0, i)
      invariant forall k :: 0 <= k <= i ==> A[k] <= A[i]
      invariant forall k :: i < k <= N - 1 ==> A[i] <= A[k]
      invariant multiset(A[..]) == multiset(old(A[..]))
    {
      if A[j] > A[j+1] {
        var temp := A[j];
        A[j] := A[j+1];
        A[j+1] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
