// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): replaced Contains with SeqToSet for easier verification */
function SeqToSet(s: seq<int>): set<int> {
  set x | x in s
}
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
  /* code modified by LLM (iteration 3): introduced ghost set 'seen' to track membership */
  var seen: set<int> := {};
  result := [];
  
  // Add elements from arr1 that are not in arr2
  for i := 0 to |arr1|
      invariant 0 <= i <= |arr1|
      invariant seen == SeqToSet(result)
      invariant forall j :: 0 <= j < i ==> (arr1[j] !in arr2 ==> arr1[j] in seen)
      invariant forall j, k :: 0 <= j < k < |result| ==> result[j] != result[k]
  {
      if arr1[i] !in arr2 && arr1[i] !in seen {
          result := result + [arr1[i]];
          seen := seen + {arr1[i]};
      }
  }
  
  // Add elements from arr2 that are not in arr1
  for i := 0 to |arr2|
      invariant 0 <= i <= |arr2|
      invariant seen == SeqToSet(result)
      invariant forall j :: 0 <= j < |arr1| ==> (arr1[j] !in arr2 ==> arr1[j] in seen)
      invariant forall j :: 0 <= j < i ==> (arr2[j] !in arr1 ==> arr2[j] in seen)
      invariant forall j, k :: 0 <= j < k < |result| ==> result[j] != result[k]
  {
      if arr2[i] !in arr1 && arr2[i] !in seen {
          result := result + [arr2[i]];
          seen := seen + {arr2[i]};
      }
  }
}
// </vc-code>
