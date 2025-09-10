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
  forall x | x in s {
    // From membership, extract an index k with s[k] == x
    var k :| 0 <= k < |s| && s[k] == x;
    assert s[minIdx] <= s[k];
    assert s[minIdx] <= x;
  }
}

lemma SortedAppendGiven(res: seq<int>, cur: seq<int>, m: int)
  requires forall i, j :: 0 <= i < j < |res| ==> res[i] <= res[j]
  requires forall x, y :: x in res && y in cur ==> x <= y
  requires m in cur
  ensures forall i, j :: 0 <= i < j < |res| + 1 ==> (res + [m])[i] <= (res + [m])[j]
{
  if |res| == 0 {
    // vacuously true
  } else {
    forall i, j | 0 <= i < j < |res| + 1 {
      if j < |res| {
        assert (res + [m])[i] <= (res + [m])[j];
      } else {
        // j == |res|
        assert res[i] <= m by {
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
  forall x, y | x in res + [m] && y in rest {
    if x in res {
      // x in res and y in rest
      assert x in res;
      // from y in rest and multiset equality, conclude y in cur
      assert multiset(rest)[y] > 0;
      assert multiset(cur)[y] == multiset(rest)[y] + multiset([m])[y];
      assert multiset(cur)[y] > 0;
      assert y in cur;
      // now apply the first requirement
      assert x <= y;
    } else {
      // x must be m
      assert x == m;
      // show y in cur
      assert multiset(rest)[y] > 0;
      assert multiset(cur)[y] == multiset(rest)[y] + multiset([m])[y];
      assert multiset(cur)[y] > 0;
      assert y in cur;
      // apply second requirement: m <= y
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
  while |cur| > 0
    invariant |res| + |cur| == |s|
    invariant multiset(res) + multiset(cur) == multiset(s)
    invariant forall i, j :: 0 <= i < j < |res| ==> res[i] <= res[j]
    invariant forall x, y :: x in res && y in cur ==> x <= y
    decreases |cur|
  {
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

    var oldCur := cur;
    RemoveAtMultiset(oldCur, minIdx);
    // oldCur[minIdx] == m
    assert oldCur[minIdx] == m;
    // minimality: for all z in oldCur, oldCur[minIdx] <= z
    MinIndexImpliesMinValue(oldCur, minIdx);

    // show m is in oldCur and m <= every element of oldCur
    assert m in oldCur;
    forall z | z in oldCur {
      assert oldCur[minIdx] <= z;
      assert oldCur[minIdx] == m;
      assert m <= z;
    }

    // multiset facts to re-establish invariant
    assert multiset(res + [m]) + multiset(rest) == multiset(res) + multiset([m]) + multiset(rest);
    assert multiset([m]) + multiset(rest) == multiset(oldCur);
    assert multiset(res) + multiset(oldCur) == multiset(s);
    assert multiset(res + [m]) + multiset(rest) == multiset(s);

    // ordering invariants
    SortedAppendGiven(res, oldCur, m);
    ResLeCurAfterAppend(res, oldCur, m, rest);

    res := res + [m];
    cur := rest;
  }
  sorted := res;
}
// </vc-code>

