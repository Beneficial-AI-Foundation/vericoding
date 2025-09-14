// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsUnique(s: seq<int>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
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
  result := [];
  var i := 0;
  while i < |arr1|
    invariant 0 <= i <= |arr1|
    invariant IsUnique(result)
    invariant forall k :: 0 <= k < i ==> (arr1[k] !in arr2 ==> arr1[k] in result)
    invariant forall x :: x in result ==> (exists k :: 0 <= k < i && arr1[k] == x && arr1[k] !in arr2)
  {
    if arr1[i] !in arr2 && arr1[i] !in result {
      result := result + [arr1[i]];
    }
    i := i + 1;
  }

  var j := 0;
  while j < |arr2|
    invariant 0 <= j <= |arr2|
    invariant IsUnique(result)
    invariant forall k :: 0 <= k < |arr1| ==> (arr1[k] !in arr2 ==> arr1[k] in result)
    invariant forall k :: 0 <= k < j ==> (arr2[k] !in arr1 ==> arr2[k] in result)
    invariant forall x :: x in result ==> 
        ((exists k :: 0 <= k < |arr1| && arr1[k] == x && arr1[k] !in arr2) ||
         (exists k :: 0 <= k < j && arr2[k] == x && arr2[k] !in arr1))
  {
    if arr2[j] !in arr1 && arr2[j] !in result {
      result := result + [arr2[j]];
    }
    j := j + 1;
  }
}
// </vc-code>
