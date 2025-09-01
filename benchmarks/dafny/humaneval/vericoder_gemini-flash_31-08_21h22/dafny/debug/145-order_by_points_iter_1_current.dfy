function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
function key(x: int): int {
  return digits_sum(x);
}

predicate is_sorted_by_key<T>(s: seq<T>, k: T -> int) {
  forall i, j :: 0 <= i < j < |s| ==> k(s[i]) <= k(s[j])
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
  sorted := s;
  var n := |sorted>;
  for i := 1 to n - 1
    invariant 0 <= i <= n
    invariant |sorted| == n
    invariant multiset(s) == multiset(sorted)
    invariant forall k, l :: 0 <= k < l < i ==> key(sorted[k]) <= key(sorted[l])
    invariant forall k :: i <= k < n ==> multiset(old(sorted[i..])) == multiset(sorted[i..])
    invariant forall k :: 0 <= k < i ==> multiset(old(sorted[k..i])) == multiset(sorted[k..i])
  {
    var j := i;
    while j > 0 && key(sorted[j-1]) > key(sorted[j])
      invariant 0 < j <= i
      invariant |sorted| == n
      invariant multiset(s) == multiset(sorted)
      invariant forall k, l :: 0 <= k < l < j ==> key(sorted[k]) <= key(sorted[l])
      invariant forall k, l :: j < k < l < i ==> key(sorted[k]) <= key(sorted[l])
      invariant forall k :: 0 <= k < j - 1 ==> key(sorted[k]) <= key(sorted[j-1]) // elements before j-1 are sorted
      invariant forall k :: j + 1 <= k < i ==> key(sorted[j]) <= key(sorted[k]) // elements after j are sorted
    {
      var temp := sorted[j];
      sorted[j] := sorted[j-1];
      sorted[j-1] := temp;
      j := j - 1;
    }
  }
}
// </vc-code>

