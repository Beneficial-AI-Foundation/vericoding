function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
lemma MinIsLessThanAnyInRest(s: seq<int>, minIndex: int)
  requires 0 <= minIndex < |s|
  requires forall j :: 0 <= j < |s| ==> digits_sum(s[minIndex]) <= digits_sum(s[j])
  ensures forall x :: x in (s[0..minIndex] + s[minIndex+1..]) ==> digits_sum(s[minIndex]) <= digits_sum(x)
{
  forall x | x in s[0..minIndex] + s[minIndex+1..]
    ensures digits_sum(s[minIndex]) <= digits_sum(x)
  {
    if x in s[0..minIndex] {
      var j :| 0 <= j < minIndex && s[j] == x;
      assert digits_sum(s[minIndex]) <= digits_sum(s[j]);
    } else {
      var j :| minIndex+1 <= j < |s| && s[j] == x;
      assert digits_sum(s[minIndex]) <= digits_sum(s[j]);
    }
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
  if s == [] {
    return [];
  }
  var n := |s|;
  var minIndex := 0;
  var i := 1;
  while i < n
    invariant 0 <= minIndex < n
    invariant 1 <= i <= n
    invariant forall j :: 0 <= j < i ==> digits_sum(s[minIndex]) <= digits_sum(s[j])
  {
    if digits_sum(s[i]) < digits_sum(s[minIndex]) {
      minIndex := i;
    }
    i := i + 1;
  }
  MinIsLessThanAnyInRest(s, minIndex);
  var rest := s[0..minIndex] + s[minIndex+1..];
  var sorted_rest := order_by_points(rest);
  return [s[minIndex]] + sorted_rest;
}
// </vc-code>

