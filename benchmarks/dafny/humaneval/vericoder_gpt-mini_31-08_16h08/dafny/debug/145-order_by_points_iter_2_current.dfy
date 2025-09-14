function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
lemma remove_index_multiset(a: seq<int>, k: int)
  requires 0 <= k < |a|
  decreases k
  ensures multiset(a) == multiset(a[..k] + a[k+1..]) + multiset([a[k]])
{
  if k == 0 {
    // a == [a[0]] + a[1..]
    assert a == [a[0]] + a[1..];
    // multiset of concat splits as sum
    assert multiset(a) == multiset([a[0]] + a[1..]);
    assert multiset([a[0]] + a[1..]) == multiset([a[0]]) + multiset(a[1..]);
    // a[..0] + a[1..] == a[1..]
    assert a[..0] + a[1..] == a[1..];
    assert multiset(a) == multiset(a[..0] + a[1..]) + multiset([a[0]]);
  } else {
    var x := a[0];
    var tail := a[1..];
    // apply induction to tail at index k-1
    remove_index_multiset(tail, k-1);
    // relate slices
    assert a[..k] + a[k+1..] == [x] + (tail[..k-1] + tail[k..]);
    // multiset(a) == multiset([x]) + multiset(tail)
    assert multiset(a) == multiset([x]) + multiset(tail);
    // from induction: multiset(tail) == multiset(tail[..k-1] + tail[k..]) + multiset([tail[k-1]])
    assert multiset(tail) == multiset(tail[..k-1] + tail[k..]) + multiset([tail[k-1]]);
    // combine
    assert multiset(a) == multiset([x]) + (multiset(tail[..k-1] + tail[k..]) + multiset([tail[k-1]]));
    // associativity of addition
    assert multiset([x]) + (multiset(tail[..k-1] + tail[k..]) + multiset([tail[k-1]])) == (multiset([x]) + multiset(tail[..k-1] + tail[k..])) + multiset([tail[k-1]]);
    // tail[k-1] == a[k]
    assert tail[k-1] == a[k];
    // multiset([x]) + multiset(tail[..k-1] + tail[k..]) == multiset([x] + (tail[..k-1] + tail[k..])) == multiset(a[..k] + a[k+1..])
    assert multiset([x]) + multiset(tail[..k-1] + tail[k..]) == multiset(a[..k] + a[k+1..]);
    // conclude
    assert multiset(a) == multiset(a[..k] + a[k+1..]) + multiset([a[k]]);
  }
}
// </vc-helpers>

// <vc-spec>
method order_by_points(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> digits_sum(sorted[i]) <= digits_sum(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var rem := s;
  var res := [];
  while |rem| > 0
    decreases |rem|
    invariant 0 <= |res| <= |s|
    invariant |res| + |rem| == |s|
    invariant multiset(res) + multiset(rem) == multiset(s)
    invariant forall i, j :: 0 <= i < j < |res| ==> digits_sum(res[i]) <= digits_sum(res[j])
    invariant (|res| == 0) || (forall j :: 0 <= j < |rem| ==> digits_sum(res[|res|-1]) <= digits_sum(rem[j]))
  {
    // find index k of a minimal digits_sum element in rem
    var k := 0;
    var min := digits_sum(rem[0]);
    var idx := 1;
    while idx < |rem|
      decreases |rem| - idx
      invariant 1 <= idx <= |rem|
      invariant 0 <= k < |rem|
      invariant min == digits_sum(rem[k])
      invariant forall j :: 0 <= j < idx ==> digits_sum(rem[k]) <= digits_sum(rem[j])
    {
      var d := digits_sum(rem[idx]);
      if d < min {
        k := idx;
        min := d;
      }
      idx := idx + 1;
    }

    // append chosen element and remove it from rem
    var oldRem := rem;
    // use lemma to relate multisets when removing index k from oldRem
    remove_index_multiset(oldRem, k);
    // use invariant before update
    assert multiset(res) + multiset(oldRem) == multiset(s);
    // expand using lemma
    assert multiset(oldRem) == multiset(oldRem[..k] + oldRem[k+1..]) + multiset([oldRem[k]]);
    assert multiset(res) + (multiset(oldRem[..k] + oldRem[k+1..]) + multiset([oldRem[k]])) == multiset(s);
    assert (multiset(res) + multiset([oldRem[k]])) + multiset(oldRem[..k] + oldRem[k+1..]) == multiset(s);

    res := res + [oldRem[k]];
    rem := oldRem[..k] + oldRem[k+1..];

    // now the multiset invariant holds for updated res and rem
    assert multiset(res) + multiset(rem) == multiset(s);
  }

  sorted := res;
}
// </vc-code>

