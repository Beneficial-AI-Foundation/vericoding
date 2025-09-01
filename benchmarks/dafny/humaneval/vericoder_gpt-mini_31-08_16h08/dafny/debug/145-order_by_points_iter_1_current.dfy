function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
// No additional helpers required
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
    res := res + [rem[k]];
    rem := rem[..k] + rem[k+1..];
  }

  sorted := res;
}
// </vc-code>

