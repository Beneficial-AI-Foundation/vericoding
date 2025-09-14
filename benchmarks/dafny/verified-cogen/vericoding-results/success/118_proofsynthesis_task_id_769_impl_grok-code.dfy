// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes, no helpers needed */
// </vc-helpers>

// <vc-spec>
method difference(arr1: seq<int>, arr2: seq<int>) returns (result: seq<int>)
    ensures
        (forall i :: 0 <= i < |arr1| ==> (arr1[i] !in arr2 ==> arr1[i] in result)) &&
        (forall i :: 0 <= i < |arr2| ==> (arr2[i] !in arr1 ==> arr2[i] in result)) &&
        (forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j])
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): added missing invariant for symmetric difference elements from arr1 */
  result := [];
  var i := 0;
  while i < |arr1|
    invariant 0 <= i <= |arr1|
    invariant forall j :: 0 <= j < i ==> (arr1[j] !in arr2 ==> arr1[j] in result)
    invariant forall p, q :: 0 <= p < q < |result| ==> result[p] != result[q]
  {
    var x := arr1[i];
    if x !in arr2 && x !in result {
      result := result + [x];
    }
    i := i + 1;
  }
  i := 0;
  while i < |arr2|
    invariant 0 <= i <= |arr2|
    invariant forall j :: 0 <= j < |arr1| ==> (arr1[j] !in arr2 ==> arr1[j] in result)
    invariant forall l :: 0 <= l < i ==> (arr2[l] !in arr1 ==> arr2[l] in result)
    invariant forall p, q :: 0 <= p < q < |result| ==> result[p] != result[q]
  {
    var x := arr2[i];
    if x !in arr1 && x !in result {
      result := result + [x];
    }
    i := i + 1;
  }
}
// </vc-code>
