// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate Unique(s: seq<int>) {
  forall i:int, j:int :: 0 <= i < j < |s| ==> s[i] != s[j]
}

lemma UniqueAppendNotIn(s: seq<int>, x: int)
  requires Unique(s)
  requires !(x in s)
  ensures Unique(s + [x])
{
}
// </vc-helpers>

// <vc-spec>
method FindDissimilar(arr1: seq<int>, arr2: seq<int>) returns (result: seq<int>)
    ensures
        (forall i :: 0 <= i < |arr1| ==> (!(arr1[i] in arr2) ==> (arr1[i] in result)))
    ensures
        (forall i :: 0 <= i < |arr2| ==> (!(arr2[i] in arr1) ==> (arr2[i] in result)))
    ensures
        (forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j])
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var i := 0;
  while i < |arr1|
    invariant 0 <= i <= |arr1|
    invariant Unique(res)
    invariant forall k :: 0 <= k < i ==> (!(arr1[k] in arr2) ==> (arr1[k] in res))
  {
    if (!(arr1[i] in arr2)) {
      if (!(arr1[i] in res)) {
        UniqueAppendNotIn(res, arr1[i]);
        res := res + [arr1[i]];
      }
    }
    i := i + 1;
  }

  var j := 0;
  while j < |arr2|
    invariant 0 <= j <= |arr2|
    invariant Unique(res)
    invariant forall k :: 0 <= k < |arr1| ==> (!(arr1[k] in arr2) ==> (arr1[k] in res))
    invariant forall k :: 0 <= k < j ==> (!(arr2[k] in arr1) ==> (arr2[k] in res))
  {
    if (!(arr2[j] in arr1)) {
      if (!(arr2[j] in res)) {
        UniqueAppendNotIn(res, arr2[j]);
        res := res + [arr2[j]];
      }
    }
    j := j + 1;
  }
  result := res;
}
// </vc-code>
