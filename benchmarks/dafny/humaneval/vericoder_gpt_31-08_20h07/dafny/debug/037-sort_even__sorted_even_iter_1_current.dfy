

// <vc-helpers>
function evenMask(n: nat): seq<bool>
  decreases n
  ensures |evenMask(n)| == n
  ensures forall i :: 0 <= i < n ==> evenMask(n)[i] == (i % 2 == 0)
{
  if n == 0 then []
  else evenMask(n - 1) + [((n - 1) % 2 == 0)]
}

lemma ZeroModOfMultiple(b: int, k: int)
  requires b > 0
  ensures (b * k) % b == 0
{
}
// </vc-helpers>

// <vc-spec>
method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var p := evenMask(|a|);
  sorted := SortSeqPred(a, p);

  assert forall i:int :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
  {
    // bounds for p
    assert |p| == |a|;
    assert 0 <= i < |p|;
    // p[i] characterizes even indices
    assert p[i] == (i % 2 == 0);
    assert !p[i];
    // by SortSeqPred postcondition
  }

  assert forall i:int, j:int ::
      0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
        sorted[2 * i] <= sorted[2 * j]
  {
    var u := 2 * i;
    var v := 2 * j;
    assert 0 <= u;
    assert u < v;
    assert
// </vc-code>

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
{
  assume{:axiom} false;
}