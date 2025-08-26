// Based on examples in class 
// The following is just plain old bubble sort.
//
// Can you find the invariants for the while loops?
// Can you annotate this?
// What about the pre/post-conditions?

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BubbleSort(A: array<int>, n: int)
modifies A
requires A.Length>=0 && n==A.Length
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall x, y :: n - i <= x < y < n ==> A[x] <= A[y]
    invariant forall x, y :: 0 <= x < n - i && n - i <= y < n ==> A[x] <= A[y]
  {
    var j := 0;
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant forall x :: 0 <= x < j ==> A[x] <= A[j]
      invariant forall x, y :: n - i <= x < y < n ==> A[x] <= A[y]
      invariant forall x, y :: 0 <= x < n - i && n - i <= y < n ==> A[x] <= A[y]
    {
      if A[j] > A[j + 1] {
        var temp := A[j];
        A[j] := A[j + 1];
        A[j + 1] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

/*Doesn't my title look all bubbly and cute? I'm trying... */