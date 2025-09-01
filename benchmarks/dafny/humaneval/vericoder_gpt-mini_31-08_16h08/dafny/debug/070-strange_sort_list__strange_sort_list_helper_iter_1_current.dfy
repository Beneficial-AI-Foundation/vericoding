

// <vc-helpers>
method FindMinIndex(s: seq<int>) returns (idx: int, minValue: int)
  requires |s| > 0
  ensures 0 <= idx < |s|
  ensures minValue == s[idx]
  ensures forall j :: 0 <= j < |s| ==> minValue <= s[j]
{
  var i := 0;
  idx := 0;
  minValue := s[0];
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= idx < |s|
    invariant minValue == s[idx]
    invariant forall j :: 0 <= j < i ==> minValue <= s[j]
  {
    if s[i] < minValue {
      minValue := s[i];
      idx := i;
    }
    i := i + 1;
  }
  // now i == |s| and invariants give the ensures
}

lemma IndexOfFromMset(s: seq<int>, x: int)
  requires multiset(s)[x] > 0
  ensures exists i :: 0 <= i < |s| && s[i] == x
  decreases |s|
{
  if |s| == 0 {
    // impossible
    assert false;
  } else if s[0] == x {
    reveal IndexOfFromMset;
    assert exists i :: 0 <= i < |s| && s[i] == x by {
      assert 0 < |s|; // trivial
      exists 0;
      assert s[0] == x;
    }
  } else {
    // multiset(s) == multiset([s[0]]) + multiset(s[1..])
    // since s[0] != x and multiset(s)[x] > 0, multiset(s[1..])[x] > 0
    assert multiset(s)[x] == (if s[0] == x then 1 else 0) + multiset(s[1..])[x];
    assert multiset(s[1..])[x] > 0;
    IndexOfFromMset(s[1..], x);
    // if exists j in s[1..] with s[1+j]==x then return j+1
    var ex := (var i :| 0 <= i < |s[1..]| && s[1..][i] == x);
    // construct witness from recursive call
    reveal IndexOfFromMset;
    // Actually extract the witness by re-proving:
    var found: int :| 0 <= found < |s[1..]| && s[1..][found] == x;
    // Use the ensures of recursive call
    assert exists i :: 0 <= i < |s[1..]| && s[1..][i] == x;
    var witness := (choose i | 0 <= i < |s[1..]| && s[1..][i] == x);
    exists witness + 1;
    assert 0 <= witness + 1 < |s|;
    assert s[witness+1] == x;
  }
}

lemma MsetPreserveLeq(m: int, a: seq<int>, b: seq<int>)
  requires multiset(a) == multiset(b)
  requires forall j :: 0 <= j < |a| ==> m <= a[j]
  ensures forall j :: 0 <= j < |b| ==> m <= b[j]
{
  // Suppose contrary there is k with b[k] < m
  if |b| == 0 {
    return;
  }
  var badExists := false;
  var badIdx := -1;
  var k := 0;
  while k < |b|
    invariant 0 <= k <= |b|
    invariant !badExists ==> forall j :: 0 <= j < k ==> m <= b[j]
    decreases |b| - k
  {
    if !(m <= b[k]) {
      badExists := true;
      badIdx := k;
      break;
    }
    k := k + 1;
  }
  if !badExists { return; }
  // we have b[badIdx] < m, call it v
  var v := b[badIdx];
  // multiset(b)[v] > 0 so multiset(a)[v] > 0
  assert multiset(b)[v] > 0;
  assert multiset(a)[v] > 0 by {
    calc {
      multiset(b)[v];
      == { }
      multiset(a)[v];
    }
  }
  // hence exists index in a with value v
  IndexOfFromMset(a, v);
  var witness := (choose i | 0 <= i < |a| && a[i] == v);
  // but by assumption m <= a[j] for all j, contradiction since a[witness] == v < m
  assert m <= a[witness];
  assert false;
}

method BuildSorted(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures multiset(sorted) == multiset(s)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  decreases |s|
{
  if |s| == 0 {
    sorted := [];
    return;
  }
  var idx, m := FindMinIndex(s);
  var srest := s[..idx] + s[idx+1..];
  var rest := BuildSorted(srest);
  // prove m <= every element of rest
  // From FindMinIndex we have forall j :: 0 <= j < |srest| ==> m <= srest[j]
  // and multiset(srest) == multiset(rest), so by lemma m <= every element of rest
  assert forall j :: 0 <= j < |srest| ==> m <= srest[j];
  MsetPreserveLeq(m, srest, rest);
  // build sorted
  sorted := [m] + rest;
  // length
  assert |sorted| == 1 + |rest|;
  assert |rest| == |srest|;
  assert |srest| + 1 == |s|;
  assert |sorted| == |s|;
  // multiset: multiset(s) == multiset(srest) + multiset([m]) and multiset(rest)==multiset(srest)
  assert multiset(s) == multiset(srest) + multiset([m]);
  assert multiset(sorted) == multiset(rest) + multiset([m]);
  assert multiset(sorted) == multiset(s);
  // sortedness: rest is sorted and m <= every element of rest implies sorted is sorted
  if |rest| >= 1 {
    assert m <= rest[0];
  }
  assert forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j] by {
    // consider cases
    // if i == 0 then sorted[0] == m <= all rest
    // if i >= 1 then use sortedness of rest
    reveal BuildSorted;
    var ii := i;
    var jj := j;
    if ii == 0 {
      // sorted[0] <= sorted[j] since sorted[j] in rest and m <= every element of rest
      assert sorted[0] == m;
      assert sorted[jj] == rest[jj-1];
      assert m <= rest[jj-1];
    } else {
      // ii-1 < jj-1 and both in rest
      assert sorted[ii] == rest[ii-1];
      assert sorted[jj] == rest[jj-1];
      // rest sorted
      assert forall a, b :: 0 <= a < b < |rest| ==> rest[a] <= rest[b];
      assert rest[ii-1] <= rest[jj-1];
    }
  }
}

method InterleaveSorted(sorted: seq<int>) returns (strange: seq<int>)
  ensures |strange| == |sorted|
  ensures forall i :: 0 <= i < |sorted| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
  ensures forall i :: 0 <= i < |sorted| && i % 2 == 1 ==> strange[i] == sorted[|sorted| - (i - 1) / 2 - 1]
{
  var n := |sorted|;
  strange := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |strange| == i
    invariant forall k :: 0 <= k < i && k % 2 == 0 ==> strange[k] == sorted[k / 2]
    invariant forall k :: 0 <= k < i && k % 2 == 1 ==> strange[k] == sorted[n - (k - 1) / 2 - 1]
  {
    if i % 2 == 0 {
      var v := sorted[i / 2];
      strange := strange + [v];
    } else {
      var v := sorted[n - (i - 1) / 2 - 1];
      strange := strange + [v];
    }
    i := i + 1;
  }
  // loop ensures give final postconditions
}
// </vc-helpers>

// <vc-spec>
method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := BuildSorted(s);
  strange := InterleaveSorted(sorted);
}
// </vc-code>

method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}