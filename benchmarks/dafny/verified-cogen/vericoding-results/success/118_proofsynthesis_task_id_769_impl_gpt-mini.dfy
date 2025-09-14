// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): NoDups predicate and supporting lemmas with explicit proofs */
predicate NoDups(s: seq<int>) { forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j] }

lemma NewElemInAppend(s: seq<int>, x: int) ensures x in s + [x] {
  assert (s + [x])[|s|] == x;
  assert x in s + [x];
}

lemma MembershipAppend(s: seq<int>, x: int, y: int) ensures y in s ==> y in s + [x] {
  if y in s {
    var i :| 0 <= i < |s| && s[i] == y;
    assert 0 <= i < |s + [x]|;
    assert (s + [x])[i] == s[i];
    assert y in s + [x];
  }
}

lemma NoDupsAppendPreserve(s: seq<int>, x: int) requires NoDups(s) && x !in s ensures NoDups(s + [x]) {
  var n := |s|;
  // Prove pairwise inequality for all indices in the extended sequence
  assert forall i, j :: 0 <= i < j < n + 1 ==> (s + [x])[i] != (s + [x])[j];
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
/* code modified by LLM (iteration 4): Build result by collecting unique elements from arr1 then arr2; maintain invariants including prefix relation */
{
  var res: seq<int> := [];
  var i := 0;
  while i < |arr1|
    invariant 0 <= i <= |arr1|
    invariant (forall k :: 0 <= k < i ==> (arr1[k] !in arr2 ==> arr1[k] in res))
    invariant NoDups(res)
    decreases |arr1| - i
  {
    var x := arr1[i];
    if x !in arr2 && x !in res {
      NoDupsAppendPreserve(res, x);
      NewElemInAppend(res, x);
      res := res + [x];
    }
    i := i + 1;
  }
  ghost var base := res;
  i := 0;
  while i < |arr2|
    invariant 0 <= i <= |arr2|
    invariant |base| <= |res|
    invariant base == res[..|base|]
    invariant (forall k :: 0 <= k < |arr1| ==> (arr1[k] !in arr2 ==> arr1[k] in base))
    invariant (forall k :: 0 <= k < i ==> (arr2[k] !in arr1 ==> arr2[k] in res))
    invariant NoDups(res)
    decreases |arr2| - i
  {
    var x := arr2[i];
    if x !in arr1 && x !in res {
      NoDupsAppendPreserve(res, x);
      NewElemInAppend(res, x);
      res := res + [x];
    }
    i := i + 1;
  }
  result := res;
}

// </vc-code>
