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
// No auxiliary helpers required for this proof.
// </vc-helpers>

// <vc-spec>
method BubbleSort(A:array<int>)
    modifies A
    ensures sorted(A)
    ensures multiset(A[..]) == multiset(old(A[..]))
// </vc-spec>
// <vc-code>
{
  var n := A.Length;
  ghost var cur: seq<int> := A[..];
  ghost var orig := multiset(cur);
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sorted_between(A, n - i, n - 1)
    invariant forall k :: n - i <= k < n ==> forall m :: 0 <= m < n - i ==> A[m] <= A[k]
    invariant cur == A[..]
    invariant multiset(A[..]) == orig
    decreases n - i
  {
    var j := 0;
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant forall m :: 0 <= m < j ==> A[m] <= A[j]
      invariant sorted_between(A, n - i, n - 1)
      invariant forall k :: n - i <= k < n ==> forall m :: 0 <= m < n - i ==> A[m] <= A[k]
      invariant cur == A[..]
      invariant multiset(A[..]) == orig
      decreases n - 1 - i - j
    {
      if A[j] > A[j+1] {
        var tmp := A[j];
        A[j] := A[j+1];
        A[j+1] := tmp;
        cur := cur[..j] + [cur[j+1]] + [cur[j]] + cur[j+2..];
      }
      j := j + 1;
    }
    // At this point j == n-1-i, so by the inner invariant:
    // forall m :: 0 <= m < n-1-i ==> A[m] <= A[n-1-i]
    i := i + 1;
  }
}
// </vc-code>

