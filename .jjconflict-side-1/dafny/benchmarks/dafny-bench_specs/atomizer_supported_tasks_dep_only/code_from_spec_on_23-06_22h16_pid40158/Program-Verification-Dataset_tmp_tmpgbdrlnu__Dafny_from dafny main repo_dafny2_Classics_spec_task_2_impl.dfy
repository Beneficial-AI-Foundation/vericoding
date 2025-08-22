// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// A version of Turing's additive factorial program [Dr. A. Turing, "Checking a large routine",
// In "Report of a Conference of High Speed Automatic Calculating Machines", pp. 67-69, 1949].

//ATOM Factorial
function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

//ATOM AdditiveFactorial
method AdditiveFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
{
  var i := 0;
  var sum := 0;
  var factorial := 1;
  
  while i < n
    invariant 0 <= i <= n
    invariant factorial == Factorial(i)
  {
    i := i + 1;
    factorial := factorial * i;
  }
  
  result := factorial;
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

//IMPL FIND
method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N;
  requires 0 <= f < N;
  modifies A;
  ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q];
{
  /* code modified by LLM (iteration 1): Implement quickselect algorithm with proper partitioning */
  var left := 0;
  var right := N - 1;
  
  while left < right
    invariant 0 <= left <= right < N
    invariant left <= f <= right
    decreases right - left
  {
    /* code modified by LLM (iteration 1): Partition around pivot using Hoare partition scheme */
    var pivot := A[right];
    var i := left - 1;
    var j := left;
    
    while j < right
      invariant left - 1 <= i < j <= right
      invariant forall k :: left <= k <= i ==> A[k] <= pivot
      invariant forall k :: i < k < j ==> A[k] > pivot
    {
      if A[j] <= pivot {
        i := i + 1;
        A[i], A[j] := A[j], A[i];
      }
      j := j + 1;
    }
    
    /* code modified by LLM (iteration 1): Place pivot in correct position */
    i := i + 1;
    A[i], A[right] := A[right], A[i];
    
    /* code modified by LLM (iteration 1): Adjust search range based on pivot position */
    if i < f {
      left := i + 1;
    } else if i > f {
      right := i - 1;
    } else {
      left := right; // Force loop termination when pivot is at target position
    }
  }
}