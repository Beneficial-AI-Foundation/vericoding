// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var diff := [];
  var seen := {};
  
  for i := 0 to |arr1|
    invariant 0 <= i <= |arr1|
    invariant forall k :: 0 <= k < i && arr1[k] !in arr2 && arr1[k] !in seen ==> arr1[k] in diff
    invariant forall k :: k in seen ==> k in diff
    invariant forall p, q :: 0 <= p < q < |diff| ==> diff[p] != diff[q]
    invariant seen == set x | x in diff
  {
    if arr1[i] !in arr2 && arr1[i] !in seen {
      diff := diff + [arr1[i]];
      seen := seen + {arr1[i]};
    }
  }
  
  for i := 0 to |arr2|
    invariant 0 <= i <= |arr2|
    invariant forall k :: 0 <= k < |arr1| && arr1[k] !in arr2 && arr1[k] !in seen ==> arr1[k] in diff
    invariant forall k :: 0 <= k < i && arr2[k] !in arr1 && arr2[k] !in seen ==> arr2[k] in diff
    invariant forall k :: k in seen ==> k in diff
    invariant forall p, q :: 0 <= p < q < |diff| ==> diff[p] != diff[q]
    invariant seen == set x | x in diff
  {
    if arr2[i] !in arr1 && arr2[i] !in seen {
      diff := diff + [arr2[i]];
      seen := seen + {arr2[i]};
    }
  }
  
  result := diff;
}
// </vc-code>
