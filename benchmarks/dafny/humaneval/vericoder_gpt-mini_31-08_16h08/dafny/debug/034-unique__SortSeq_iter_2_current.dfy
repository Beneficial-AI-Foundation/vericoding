method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma RemoveAtMultiset<T>(s: seq<T>, idx: int)
  requires 0 <= idx < |s|
  ensures multiset(s[..idx] + s[idx+1..]) + multiset([s[idx]]) == multiset(s)
{
  // s == s[..idx] + [s[idx]] + s[idx+1..]
  calc {
    multiset(s);
    == {
    }
    multiset(s[..idx] + [s[idx]] + s[idx+1..]);
    == {
    }
    multiset(s[..idx]) + multiset([s[idx]]) + multiset(s[idx+1..]);
    == {
    }
    multiset(s[..idx] + s[idx+1..]) + multiset([s[idx]]);
  }
}

lemma MinIndexImpliesMinValue(s: seq<int>, minIdx: int)
  requires 0 <= minIdx < |s|
  requires forall k :: 0 <= k < |s| ==> s[minIdx] <= s[k]
  ensures forall x :: x in s ==> s[minIdx] <= x
{
  // if x in s then exists k such that x == s[k], and then use the forall k hypothesis
  reveal_multiset; // sometimes helps Dafny with sequence facts
  var k := 0;
  // Proof by unfolding membership
  // For each x in s there is an index k; we can reason using indexing:
  // This lemma is trivial from the second requires clause.
}

lemma SortedAppendGiven(res: seq<int>, cur: seq<int>, m: int)
  requires forall i, j :: 0 <= i < j < |res| ==> res[i] <= res[j]
  requires forall x, y :: x in res && y in cur ==> x <= y
  requires m in cur
  ensures forall i, j :: 0 <= i < j < |res| + 1 ==> (res + [m])[i] <= (res + [m])[j]
{
  // Two cases for positions i < j in res + [m]:
  // 1) j < |res| : follows from res sorted
  // 2) j == |res| : then i < |res| and need res[i] <= m, which follows from second requirement
  if |res| == 0 {
    // vacuously true: no i < j < 1 except none
  } else {
    // prove general case
    forall i, j | 0 <= i < j < |res| + 1 {
      if j < |res| {
        assert (res + [m])[i] <= (res + [m])[j];
      } else {
        // j == |res|
        // then (res + [m])[j] == m and for i < |res|, (res + [m])[i] == res[i]
        assert res[i] <= m by {
          // res[i] in res and m in cur, use second require
          assert res[i] in res;
          assert m in cur;
        }
        assert (res + [m])[i] <= (res + [m])[j];
      }
    }
  }
}

lemma ResLeCurAfterAppend(res: seq<int>, cur: seq<int>, m: int, rest: seq<int>)
  requires forall x, y :: x in res && y in cur ==> x <= y
  requires forall z :: z in cur ==> m <= z
  requires m in cur
  requires multiset(rest) + multiset([m]) == multiset(cur)
  ensures forall x, y :: x in res + [m] && y in rest ==> x <= y
{
  // If x in res then x <= y because y in rest subset of cur and first requirement holds.
  // If x == m then m <= y because of second requirement.
  forall x, y | x in res + [m] && y in rest {
    if x in res {
      // x in res and y in cur (since rest subset of cur from multiset fact), so x <= y
      assert x in res;
      // we need y in cur; from multiset(rest) + multiset([m]) == multiset(cur),
      // every element of rest is in cur. Use that as a fact by reasoning about membership:
      assert y in cur;
      assert x <= y by {
      }
    } else {
      // x must be the last element m
      assert x == m;
      // y in rest implies y in cur, so m <= y
      assert y in cur;
      assert m <= y;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var cur := s;
  var res : seq<int> := [];
  // invariants: number of elements preserved, multiset preserved, res sorted,
  // and every element of res <= every element of cur
  while |cur| > 0
    invariant |res| + |cur| == |s|
    invariant multiset(res) + multiset(cur) == multiset(s)
    invariant forall i, j :: 0 <= i < j < |res| ==> res[i] <= res[j]
    invariant forall x, y :: x in res && y in cur ==> x <= y
    decreases |cur|
  {
    // find minimal element index in cur
    var minIdx := 0;
    var i := 1;
    while i < |cur|
      invariant 0 <= minIdx < |cur|
      invariant 0 <= i <= |cur|
      invariant forall k :: 0 <= k < i ==> cur[minIdx] <= cur[k]
      decreases |cur| - i
    {
      if cur[i] < cur[minIdx] {
        minIdx := i;
      }
      i := i + 1;
    }
    var m := cur[minIdx];
    var rest := cur[..minIdx] + cur[minIdx+1..];

    // Use lemmas to establish the loop invariants after the update.
    var oldCur := cur;
    // multiset(rest) + multiset([m]) == multiset(oldCur)
    RemoveAtMultiset(oldCur, minIdx);
    // minimality: for all z in oldCur, oldCur[minIdx] <= z
    MinIndexImpliesMinValue(oldCur, minIdx);
    // Now prove multiset(res + [m]) + multiset(rest) == multiset(s)
    assert multiset(res + [m]) + multiset(rest) == multiset(res) + multiset([m]) + multiset(rest);
    assert multiset([m]) + multiset(rest) == multiset(oldCur);
    assert multiset(res) + multiset(oldCur) == multiset(s);
    // by transitivity
    assert multiset(res + [m]) + multiset(rest) == multiset(s);

    // Prove ordering invariants:
    // res + [m] is sorted
    SortedAppendGiven(res, oldCur, m);
    // every element of res + [m] <= every element of rest
    // from MinIndexImpliesMinValue we know forall z in oldCur ==> m <= z, and rest subset of oldCur
    ResLeCurAfterAppend(res, oldCur, m, rest);

    // update res and cur
    res := res + [m];
    cur := rest;
  }
  sorted := res;
}
// </vc-code>

