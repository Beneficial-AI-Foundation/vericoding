function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>

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
  var res := [];
  for i := 0 to s.Len - 1 {
    var elem := s[i];
    var pos := res.Len;
    while pos > 0 && digits_sum(res[pos-1]) > digits_sum(elem) {
      pos := pos - 1;
    }
    res := res[..pos] + [elem] + res[pos..];
  }
  return res;
}
// </vc-code>

