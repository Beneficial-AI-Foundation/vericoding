function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
function compare_by_digits_sum(a: int, b: int): bool {
  digits_sum(a) <= digits_sum(b)
}

lemma SortedByDigitsSumImpliesOrder(s: seq<int>)
  ensures forall i, j :: 0 <= i < j < |s| ==> compare_by_digits_sum(s[i], s[j])
{
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
method OrderByPoints(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> digits_sum(sorted[i]) <= digits_sum(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  sorted := s;
  var n := |s|;
  if n <= 1 {
    return;
  }
  
  var i := 0;
  while i < n - 1
    invariant 0 <= i < n
    invariant forall k, l :: 0 <= k < l < i ==> digits_sum(sorted[k]) <= digits_sum(sorted[l])
    invariant multiset(sorted) == multiset(s)
    invariant |sorted| == |s|
  {
    var min_idx := i;
    var j := i + 1;
    while j < n
      invariant i <= min_idx < n
      invariant i < j <= n
      invariant forall k :: i <= k < j ==> digits_sum(sorted[min_idx]) <= digits_sum(sorted[k])
      invariant multiset(sorted) == multiset(s)
      invariant |sorted| == |s|
    {
      if digits_sum(sorted[j]) < digits_sum(sorted[min_idx]) {
        min_idx := j;
      }
      j := j + 1;
    }
    if min_idx != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[min_idx]];
      sorted := sorted[min_idx := temp];
    }
    i := i + 1;
  }
}
// </vc-code>
