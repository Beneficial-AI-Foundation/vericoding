type SortSeqState = seq<(int, int)>
function less(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  x < u || (x == u && y > v)
}
function less_eq(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  (x == u && y == v) || less(a, b)
}
method get_row(lst: seq<seq<int>>, x: int) returns (pos: SortSeqState)
  // post-conditions-start
  ensures forall i :: 0 <= i < |pos| ==> (
    var (a, b) := pos[i];
    0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
  )
  ensures forall i, j :: 0 <= i < |lst| && 0 <= j < |lst[i]| && lst[i][j] == x ==> (i, j) in pos
  ensures forall i, j :: 0 <= i < j < |pos| ==> less_eq(pos[i], pos[j])
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultisetMovePreserve<T>(oldRes: seq<T>, oldCur: seq<T>, m: int)
  requires 0 <= m < |oldCur|
  ensures multiset(oldRes + [oldCur[m]] + oldCur[..m] + oldCur[m+1..]) == multiset(oldRes + oldCur)
{
  var prefix := oldCur[..m];
  var e := oldCur[m];
  var suffix := oldCur[m+1..];
  assert oldCur == prefix + [e] + suffix;
  // multiset(oldRes + oldCur) == multiset(oldRes + (prefix + [e] + suffix))
  assert multiset(oldRes + oldCur) == multiset(oldRes + (prefix + [e] + suffix));
  // expand multisets using distributivity of multiset over concatenation
  assert multiset(oldRes + (prefix + [e] + suffix)) == multiset(oldRes) + multiset(prefix + [e] + suffix);
  assert multiset(oldRes + [e] + prefix + suffix) == multiset(oldRes) + multiset([e] + prefix + suffix);
  // break down the inner multisets
  assert multiset(prefix + [e] + suffix) == multiset(prefix) + multiset([e]) + multiset(suffix);
  assert multiset([e] + prefix + suffix) == multiset([e]) + multiset(prefix) + multiset(suffix);
  // multiset addition is commutative, so these sums are equal
  assert multiset(prefix) + multiset([e]) + multiset(suffix) == multiset([e]) + multiset(prefix) + multiset(suffix);
  assert multiset(prefix + [e] + suffix) == multiset([e] + prefix + suffix);
  // combine back to sequence multisets
  assert multiset(oldRes) + multiset(prefix + [e] + suffix) == multiset(oldRes) + multiset([e] + prefix + suffix);
  assert multiset(oldRes + (prefix + [e] + suffix)) == multiset(oldRes + [e] + prefix + suffix);
  // conclude
  assert multiset(oldRes + [e] + prefix + suffix) == multiset(oldRes + oldCur);
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var res: SortSeqState := [];
  var cur := s;
  while |cur| > 0
    invariant multiset(res + cur) == multiset(s)
    invariant forall i, j :: 0 <= i < j < |res| ==> less_eq(res[i], res[j])
    invariant forall i :: 0 <= i < |res| ==> forall j :: 0 <= j < |cur| ==> less_eq(res[i], cur[j])
    invariant |res| + |cur| == |s|
    decreases |cur|
  {
    // find minimal index m in cur
    var m := 0;
    var j := 1;
    while j < |cur|
      invariant 0 <= m < |cur|
      invariant 1 <= j <= |cur|
      invariant forall k :: 0 <= k < j ==> less_eq(cur[m], cur[k])
      decreases |cur| - j
    {
      if less(cur[j], cur[m]) {
        m := j;
      }
      j := j + 1;
    }

    // save old values to reason about preservation of invariants
    var oldRes := res;
    var oldCur := cur;
    // from loop invariant before updating, we know multiset(oldRes + oldCur) == multiset(s)
    assert multiset(oldRes + oldCur) == multiset(s);
    // also from invariants before update:
    assert forall i, j :: 0 <= i < |oldRes| ==> 0 <= j < |oldCur| ==> less_eq(oldRes[i], oldCur[j]);
    assert forall i, j :: 0 <= i < j < |oldRes| ==> less_eq(oldRes[i], oldRes[j]);
    // from inner loop (j finished at |cur|) we have minimality of m over oldCur
    assert forall k :: 0 <= k < |oldCur| ==> less_eq(oldCur[m], oldCur[k]);

    // perform move: append minimal element to res and remove it from cur
    res := oldRes + [oldCur[m]];
    cur := oldCur[..m] + oldCur[m+1..];

    // update length invariant: |res| == |oldRes| + 1 and |cur| == |oldCur| - 1
    assert |res| == |oldRes| + 1;
    assert |oldCur[..m]| == m;
    assert |oldCur[m+1..]| == |oldCur| - m - 1;
    assert |cur| == m + (|oldCur| - m - 1);
    assert |cur| == |oldCur| - 1;
    assert |res| + |cur| == |s|;

    // update multiset invariant: moving one element from cur to res preserves multiset(res+cur)
    MultisetMovePreserve(oldRes, oldCur, m);
    assert multiset(res + cur) == multiset(oldRes + oldCur);
    assert multiset(res + cur) == multiset(s);

    // update ordering invariants:
    // 1) res remains sorted: all oldRes elements <= oldCur[m] and oldRes was sorted
    assert forall i, j :: 0 <= i < j < |res| ==> less_eq(res[i], res[j]);
    // 2) every element in res is <= every element in cur:
    //    for old elements of res this held before; for the newly appended element oldCur[m], it is <= all oldCur[k]
    assert forall i :: 0 <= i < |res| ==> forall j :: 0 <= j < |cur| ==> less_eq(res[i], cur[j]);
  }
  sorted := res;
}
// </vc-code>

