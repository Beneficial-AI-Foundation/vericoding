// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced 'function method' with 'function' to satisfy syntax */
function Min(a: int, b: int): int {
  if a <= b then a else b
}
// </vc-helpers>

// <vc-spec>
method MergeSortedLists(arr1: array<int>, arr2: array<int>) returns (result: array<int>)
    requires 
        forall i, j :: 0 <= i < j < arr1.Length ==> arr1[i] <= arr1[j]
    requires
        forall i, j :: 0 <= i < j < arr2.Length ==> arr2[i] <= arr2[j]
    ensures
        forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]
    ensures
        result.Length == arr1.Length + arr2.Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented merge without axioms and with safe indexing/invariants */
  var n1 := arr1.Length;
  var n2 := arr2.Length;
  result := new int[n1 + n2];
  var i1 := 0;
  var i2 := 0;
  var k := 0;
  while k < result.Length
    invariant 0 <= i1 <= n1
    invariant 0 <= i2 <= n2
    invariant 0 <= k <= result.Length
    invariant k == i1 + i2
    invariant forall p, q :: 0 <= p < q < k ==> result[p] <= result[q]
    invariant k == 0 || (i1 < n1 ==> result[k-1] <= arr1[i1])
    invariant k == 0 || (i2 < n2 ==> result[k-1] <= arr2[i2])
    decreases result.Length - k
  {
    if i1 < n1 && (i2 == n2 || arr1[i1] <= arr2[i2]) {
      result[k] := arr1[i1];
      i1 := i1 + 1;
      k := k + 1;
    } else {
      // Here either i1 == n1 (hence i2 < n2) or arr1[i1] > arr2[i2] with i2 < n2
      result[k] := arr2[i2];
      i2 := i2 + 1;
      k := k + 1;
    }
  }
}
// </vc-code>
