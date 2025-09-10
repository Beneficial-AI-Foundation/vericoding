function comparison(a : string, b : string, i : int): bool
    requires 0 <= i <= |a| && 0 <= i <= |b|
    decreases |a| - i
    decreases |b| - i
    ensures (a == b) ==> comparison(a, b, i)
{
    if (i < |a| && i < |b|) then
        if a[i] < b[i] then
            true
        else if a[i] > b[i] then
            false
        else
            comparison(a, b, i + 1)
    else
        if |a| <= |b| then
            true
        else
            false
}
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
{
  assume{:axiom} false;
}

// <vc-helpers>
method find_min_index(a: seq<string>) returns (k: int)
    requires |a| > 0
    ensures 0 <= k < |a|
    ensures forall j :: 0 <= j < |a| ==> |a[k]| <= |a[j]|
    decreases |a|
{
  var i := 1;
  var min := 0;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant 0 <= min < i
    invariant forall j :: 0 <= j < i ==> |a[min]| <= |a[j]|
  {
    if |a[i]| < |a[min]| {
      min := i;
    }
    i := i + 1;
  }
  k := min;
}

lemma multiset_remove_at<T>(a: seq<T>, k: int)
  requires 0 <= k < |a|
  ensures multiset(a[..k] + a[k+1..]) + multiset([a[k]]) == multiset(a)
  decreases k
{
  if k == 0 {
    // a == [a[0]] + a[1..]
    assert a == [a[0]] + a[1..];
    assert multiset(a) == multiset([a[0]] + a[1..]);
    assert multiset([a[0]] + a[1..]) == multiset([a[0]]) + multiset(a[1..]);
    assert a[..0] + a[1..] == a[1..];
    assert multiset(a[..0] + a[1..]) == multiset(a[1..]);
    // combine equalities to get the desired result
    assert multiset(a[..0] + a[1..]) + multiset([a[0]]) == multiset(a[1..]) + multiset([a[0]]);
    assert multiset(a[1..]) + multiset([a[0]]) == multiset([a[0]]) + multiset(a[1..]);
    assert multiset([a[0]]) + multiset(a[1..]) == multiset([a[0]] + a[1..]);
    assert multiset([a[0]] + a[1..]) == multiset(a);
    assert multiset(a[..0] + a[1..]) + multiset([a[0]]) == multiset(a);
  } else {
    var b := a[1..];
    multiset_remove_at(b, k - 1);
    // a[..k] == [a[0]] + b[..k-1]
    // a[k] == b[k-1]
    // a[k+1..] == b[k..]
    assert a[..k] + a[k+1..] == [a[0]] + (b[..k-1] + b[k..]);
    assert multiset(a[..k] + a[k+1..]) == multiset([a[0]]) + multiset(b[..k-1] + b[k..]);
    // from recursive call: multiset(b[..k-1] + b[k..]) + multiset([b[k-1]]) == multiset(b)
    assert multiset(b[..k-1] + b[k..]) + multiset([b[k-1]]) == multiset(b);
    // combine to get the result for a
    assert multiset(a[..k] + a[k+1..]) + multiset([a[k]]) == multiset([a[0]]) + (multiset(b[..k-1] + b[k..]) + multiset([b[k-1]]));
    assert multiset([a[0]]) + (multiset(b[..k-1] + b[k..]) + multiset([b[k-1]])) == multiset([a[0]]) + multiset(b);
    assert multiset([a[0]]) + multiset(b) == multiset([a[0]] + b);
    assert multiset([a[0]] + b) == multiset(a);
    assert multiset(a[..k] + a[k+1..]) + multiset([a[k]]) == multiset(a);
  }
}
// </vc-helpers>

// <vc-spec>
method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
// </vc-spec>
// <vc-code>
{
  var acc: seq<string> := [];
  var rem := list;
  while |rem| > 0
    invariant 0 <= |rem| <= |list|
    invariant |acc| + |rem| == |list|
    invariant multiset(acc) + multiset(rem) == multiset(list)
    invariant forall i :: 0 <= i < |acc| ==> |acc[i]| % 2 == 0
    invariant forall i :: 0 <= i < |rem| ==> |rem[i]| % 2 == 0
    invariant forall x, y :: 0 <= x < y < |acc| ==> |acc[x]| <= |acc[y]|
    invariant forall x, y :: 0 <= x < |acc| && 0 <= y < |rem| ==> |acc[x]| <= |rem[y]|
  {
    var k := find_min_index(rem);
    var s := rem[k];
    var oldAcc := acc;
    var oldRem := rem;
    // perform the move of element s from rem to acc
    acc := oldAcc + [s];
    rem := oldRem[..k] + oldRem[k+1..];
    // prove the multiset invariant is preserved
    // multiset(oldRem[..k] + oldRem[k+1..]) + multiset([s]) == multiset(oldRem)
    multiset_remove_at(oldRem, k);
    assert s == oldRem[k];
    // now combine to get multiset(acc) + multiset(rem) == multiset(list)
    assert multiset(acc) + multiset(rem) == multiset(oldAcc + [s]) + multiset(oldRem[..k] + oldRem[k+1..]);
    assert multiset(oldAcc + [s]) + multiset(oldRem[..k] + oldRem[k+1..]) == multiset(oldAcc) + multiset([s]) + multiset(oldRem[..k] + oldRem[k+1..]);
    assert multiset([s]) + multiset(oldRem[..k] + oldRem[k+1..]) == multiset(oldRem);
    assert multiset(oldAcc) + multiset(oldRem) == multiset(list);
  }
  sorted := acc;
}
// </vc-code>

method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
  assume{:axiom} false;
}