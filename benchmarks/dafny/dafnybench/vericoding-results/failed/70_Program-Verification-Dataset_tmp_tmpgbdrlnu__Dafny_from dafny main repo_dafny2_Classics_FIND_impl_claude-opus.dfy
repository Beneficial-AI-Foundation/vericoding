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
ghost predicate Partitioned(A: array<int>, pivot: int, lo: int, hi: int)
  reads A
  requires 0 <= lo <= pivot < hi <= A.Length
{
  (forall i :: lo <= i <= pivot ==> A[i] <= A[pivot]) &&
  (forall i :: pivot < i < hi ==> A[pivot] <= A[i])
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
  var lo := 0;
  var hi := N - 1;
  
  while lo < hi
    invariant 0 <= lo <= f <= hi < N
    invariant forall p, q :: 0 <= p < lo && hi < q < N ==> A[p] <= A[q]
    invariant forall p :: 0 <= p < lo ==> forall q :: lo <= q <= hi ==> A[p] <= A[q]
    invariant forall p :: hi < p < N ==> forall q :: lo <= q <= hi ==> A[q] <= A[p]
  {
    // Partition around A[f]
    var pivot := A[f];
    var i := lo;
    var j := hi;
    
    // Move pivot to position lo temporarily
    A[f], A[lo] := A[lo], A[f];
    
    while i < j
      invariant lo <= i <= j <= hi
      invariant A[lo] == pivot
      invariant forall k :: lo < k <= i ==> A[k] <= pivot
      invariant forall k :: j < k <= hi ==> pivot <= A[k]
      invariant forall p, q :: 0 <= p < lo && hi < q < N ==> A[p] <= A[q]
      invariant forall p :: 0 <= p < lo ==> forall q :: lo <= q <= hi ==> A[p] <= A[q]
      invariant forall p :: hi < p < N ==> forall q :: lo <= q <= hi ==> A[q] <= A[p]
    {
      // Move i right while A[i+1] <= pivot
      while i < j && A[i + 1] <= pivot
        invariant lo <= i <= j <= hi
        invariant A[lo] == pivot
        invariant forall k :: lo < k <= i ==> A[k] <= pivot
        invariant forall k :: j < k <= hi ==> pivot <= A[k]
      {
        i := i + 1;
      }
      
      // Move j left while A[j] > pivot
      while i < j && A[j] > pivot
        invariant lo <= i <= j <= hi
        invariant A[lo] == pivot
        invariant forall k :: lo < k <= i ==> A[k] <= pivot
        invariant forall k :: j < k <= hi ==> pivot <= A[k]
      {
        j := j - 1;
      }
      
      // Swap if needed
      if i < j {
        A[i + 1], A[j] := A[j], A[i + 1];
        i := i + 1;
        if i < j {
          j := j - 1;
        }
      }
    }
    
    // Place pivot in final position
    A[lo], A[i] := A[i], A[lo];
    
    // Adjust lo or hi based on where f is relative to pivot position
    if f < i {
      hi := i - 1;
    } else if f > i {
      lo := i + 1;
    } else {
      // f == i, we're done
      break;
    }
  }
}
// </vc-code>

