// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// A version of Turing's additive factorial program [Dr. A. Turing, "Checking a large routine",
// In "Report of a Conference of High Speed Automatic Calculating Machines", pp. 67-69, 1949].

//ATOM 
ghost function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}


//IMPL AdditiveFactorial
method AdditiveFactorial(n: nat) returns (u: nat)
  ensures u == Factorial(n);
{
  if n == 0 {
    u := 1;
    return;
  }
  
  u := 1;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1;
    invariant u == Factorial(i - 1);
  {
    u := u * i;
    i := i + 1;
  }
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
  /* code modified by LLM (iteration 1): implementing quickselect to partition around f */
  var left := 0;
  var right := N - 1;
  
  while left < right
    invariant 0 <= left <= f <= right < N;
    invariant forall p :: 0 <= p < left ==> forall q :: right < q < N ==> A[p] <= A[q];
    invariant forall p :: 0 <= p < left ==> forall q :: left <= q <= right ==> A[p] <= A[q];
    invariant forall p :: left <= p <= right ==> forall q :: right < q < N ==> A[p] <= A[q];
  {
    /* code modified by LLM (iteration 1): choose pivot and partition */
    var pivot := A[f];
    var i := left;
    var j := right;
    
    while i < j
      invariant left <= i <= j <= right;
      invariant forall p :: left <= p < i ==> A[p] <= pivot;
      invariant forall q :: j < q <= right ==> A[q] >= pivot;
    {
      while i < j && A[i] <= pivot
        invariant left <= i <= j <= right;
        invariant forall p :: left <= p < i ==> A[p] <= pivot;
        invariant forall q :: j < q <= right ==> A[q] >= pivot;
      {
        i := i + 1;
      }
      
      while i < j && A[j] >= pivot
        invariant left <= i <= j <= right;
        invariant forall p :: left <= p < i ==> A[p] <= pivot;
        invariant forall q :: j < q <= right ==> A[q] >= pivot;
      {
        j := j - 1;
      }
      
      if i < j {
        A[i], A[j] := A[j], A[i];
      }
    }
    
    /* code modified by LLM (iteration 1): determine which side contains f and continue */
    if f < i {
      right := i - 1;
    } else if f > i {
      left := i + 1;
    } else {
      break;
    }
  }
  
  /* code modified by LLM (iteration 1): additional sorting to ensure postcondition */
  var k := 0;
  while k < N - 1
    invariant 0 <= k < N;
    invariant forall p, q :: 0 <= p < q < N && (p <= f || q <= f) ==> A[p] <= A[q];
  {
    var minIdx := k;
    var j := k + 1;
    
    while j < N
      invariant k <= minIdx < N;
      invariant k < j <= N;
      invariant forall p :: k <= p < j ==> A[minIdx] <= A[p];
    {
      if A[j] < A[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    
    if minIdx != k {
      A[k], A[minIdx] := A[minIdx], A[k];
    }
    
    k := k + 1;
  }
}