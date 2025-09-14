// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed IndexInArrayLemma to be a proper lemma body and correct logic */
lemma IndexInArrayLemma(k: int, arr: array<int>)
  ensures k in arr[..] <==> (exists i :: 0 <= i < arr.Length && arr[i] == k)
{
  // The lemma body establishes the equivalence
  // Left side: k in arr[..] means k appears in the sequence
  // Right side: there exists an index i where arr[i] equals k
  if k in arr[..] {
    // If k is in the array, find the index where it appears
    var index :| 0 <= index < arr.Length && arr[index] == k;
    // The existence follows automatically
  } else {
    // If k is not in the array, no such index exists
    assert forall i :: 0 <= i < arr.Length ==> arr[i] != k;
  }
}
// </vc-helpers>

// <vc-spec>
method AnyValueExists(arr1: array<int>, arr2: array<int>) returns (result: bool)
    ensures result == exists k :: 0 <= k < arr1.Length && k in arr2[..]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed logic to correctly check if any arr1 index exists in arr2 */
{
  var k := 0;
  while k < arr1.Length
    invariant 0 <= k <= arr1.Length
    invariant forall i :: 0 <= i < k ==> !(i in arr2[..])
  {
    if k in arr2[..] {
      result := true;
      return;
    }
    k := k + 1;
  }
  result := false;
}
// </vc-code>
