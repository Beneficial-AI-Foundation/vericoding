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
//     forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q]).

// <vc-helpers>
method Partition(A: array<int>, lo: int, hi: int, pivotIndex: int) returns (newPivotIndex: int)
  requires 0 <= lo <= pivotIndex <= hi < A.Length
  modifies A
  ensures lo <= newPivotIndex <= hi
  ensures forall i :: lo <= i < newPivotIndex ==> A[i] <= A[newPivotIndex]
  ensures forall i :: newPivotIndex < i <= hi ==> A[newPivotIndex] <= A[i]
  ensures forall i :: 0 <= i < lo ==> A[i] == old(A[i])
  ensures forall i :: hi < i < A.Length ==> A[i] == old(A[i])
{
  var pivotValue := A[pivotIndex];
  A[pivotIndex] := A[hi];
  A[hi] := pivotValue;
  
  var storeIndex := lo;
  var i := lo;
  
  while i < hi
    invariant lo <= storeIndex <= i <= hi
    invariant forall j :: lo <= j < storeIndex ==> A[j] <= pivotValue
    invariant forall j :: storeIndex <= j < i ==> A[j] > pivotValue
    invariant A[hi] == pivotValue
    invariant forall j :: 0 <= j < lo ==> A[j] == old(A[j])
    invariant forall j :: hi < j < A.Length ==> A[j] == old(A[j])
  {
    if A[i] <= pivotValue {
      var temp := A[storeIndex];
      A[storeIndex] := A[i];
      A[i] := temp;
      storeIndex := storeIndex + 1;
    }
    i := i + 1;
  }
  
  A[hi] := A[storeIndex];
  A[storeIndex] := pivotValue;
  newPivotIndex := storeIndex;
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
  if N <= 1 {
    return;
  }
  
  var lo := 0;
  var hi := N - 1;
  
  while lo < hi
    invariant 0 <= lo <= f <= hi < N
    invariant forall p :: 0 <= p < lo ==> forall q :: hi < q < N ==> A[p] <= A[q]
    invariant forall p :: 0 <= p < lo ==> forall q :: f <= q <= hi ==> A[p] <= A[q]
    invariant forall p :: lo <= p <= f ==> forall q :: hi < q < N ==> A[p] <= A[q]
    decreases hi - lo
  {
    var pivotIndex := Partition(A, lo, hi, f);
    
    if pivotIndex == f {
      break;
    } else if pivotIndex < f {
      // From partition: A[i] <= A[pivotIndex] for lo <= i < pivotIndex
      //                 A[pivotIndex] <= A[i] for pivotIndex < i <= hi
      // Since pivotIndex < f, all elements in [lo, pivotIndex] are <= A[pivotIndex]
      // and A[pivotIndex] <= all elements in [pivotIndex+1, hi]
      
      // Moving lo to pivotIndex + 1 maintains invariants:
      // - Elements in [0, pivotIndex] now satisfy the "left of search range" properties
      // - Elements in [pivotIndex+1, hi] maintain their properties
      
      // Key insight: A[p] <= A[pivotIndex] <= A[q] for p in [lo, pivotIndex], q in [f, hi]
      assert forall p :: lo <= p <= pivotIndex ==> forall q :: f <= q <= hi ==> A[p] <= A[q];
      
      lo := pivotIndex + 1;
    } else {
      // pivotIndex > f, so A[i] <= A[pivotIndex] for lo <= i < pivotIndex
      //                    A[pivotIndex] <= A[i] for pivotIndex < i <= hi
      // Since f < pivotIndex, all elements in [lo, f] are <= A[pivotIndex]
      // and A[pivotIndex] <= all elements in [pivotIndex, hi]
      
      // Moving hi to pivotIndex - 1 maintains invariants:
      // - Elements in [pivotIndex, hi] now satisfy the "right of search range" properties
      
      // Key insight: A[p] <= A[pivotIndex] <= A[q] for p in [lo, f], q in [pivotIndex, hi]
      assert forall p :: lo <= p <= f ==> forall q :: pivotIndex <= q <= hi ==> A[p] <= A[q];
      
      hi := pivotIndex - 1;
    }
  }
  
  // When loop exits, lo >= hi, but we maintain lo <= f <= hi, so lo == hi == f
  // The invariants then give us the postcondition
  assert lo == hi;
  assert lo == f;
}
// </vc-code>