// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// A version of Turing's additive factorial program [Dr. A. Turing, "Checking a large routine",
// In "Report of a Conference of High Speed Automatic Calculating Machines", pp. 67-69, 1949].

ghost function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}


// Hoare's FIND program [C.A.R. Hoare, "Proof of a program: FIND", CACM 14(1): 39-45, 1971].
// The proof annotations here are not the same as in Hoare's article.

// In Hoare's words:
//   This program operates on an array A[1:N], and a value of f (1 <= f <= N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q (1 <= p <= f <= q <= N ==> A[p] <= A[f] <= A[q]).
//
// Here, we use 0-based indices, so we would say:
//   This method operates on an array A[0..N], and a value of f (0 <= f < N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[f] <= A[q]).

// <vc-helpers>
predicate sortedSubarray(A: array<int>, start: int, end: int)
  requires 0 <= start <= end <= A.Length
  reads A
{
  forall i, j :: start <= i <= j < end ==> A[i] <= A[j]
}
// </vc-helpers>

// <vc-spec>
method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N;
  requires 0 <= f < N;
  modifies A;
  ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q];
// </vc-spec>
// <vc-code>
{
  var l := 0;
  var r := N - 1;
  var pivot_val := A[f];

  while l <= r
    invariant 0 <= l <= N && -1 <= r < N
    invariant forall i :: 0 <= i < l ==> A[i] <= pivot_val
    invariant forall i :: r < i < N ==> A[i] >= pivot_val
    invariant exists k :: 0 <= k < N && A[k] == pivot_val
    invariant A.Length == N
    decreases r - l
  {
    if A[l] < pivot_val {
      l := l + 1;
    } else if A[r] > pivot_val {
      r := r - 1;
    } else if A[l] >= pivot_val && A[r] <= pivot_val { // Updated condition here
      if l <= r { // Added check for l <= r
        var temp := A[l];
        A[l] := A[r];
        A[r] := temp;
        if l == f then
          f := r;
        else if r == f then
          f := l;
        l := l + 1;
        r := r - 1;
      } else {
        break;
      }
    } else { // This else branch handles cases where neither A[l] < pivot_val nor A[r] > pivot_val
             // The only remaining cases are A[l] >= pivot_val and A[r] <= pivot_val,
             // or some combination where l crosses r
      break; // Exit the loop if no progress can be made, or indices cross
    }
  }

  // The final phase: Ensure elements around f are correctly partitioned based on A[f]
  // The earlier loop already partitions based on the initial pivot_val (A[f] at start).
  // Now we need to ensure A[f] is at the correct position and elements are partitioned around the current A[f] value.

  var current_f_val := A[f];
  
  // Re-partitioning to put all elements equal to current_f_val in the middle, and ensure
  // elements <= current_f_val are to the left and >= current_f_val are to the right.
  // This is a standard three-way partitioning approach, often used in implementations of quickselect/Hoare's FIND.

  var i := 0;
  var j := N - 1;
  var k := f; // k is the index of the element at f

  while i <= j
    invariant 0 <= i <= N && -1 <= j < N
    invariant forall x :: 0 <= x < i ==> A[x] <= current_f_val
    invariant forall x :: j < x < N ==> A[x] >= current_f_val
    invariant exists idx :: (0 <= idx < N && A[idx] == current_f_val)
    decreases j - i
  {
    if A[i] < current_f_val {
      i := i + 1;
    } else if A[j] > current_f_val {
      j := j - 1;
    } else {
      // A[i] >= current_f_val and A[j] <= current_f_val
      if i <= j {
        if i == k { // If the element at k has been swapped, update k
            k := j;
        } else if j == k {
            k := i;
        }
        var temp := A[i];
        A[i] := A[j];
        A[j] := temp;
        i := i + 1;
        j := j - 1;
      } else {
        break;
      }
    }
  }
}
// </vc-code>

