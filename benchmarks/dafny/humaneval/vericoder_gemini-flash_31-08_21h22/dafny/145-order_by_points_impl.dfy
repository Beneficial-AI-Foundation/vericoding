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
  var n := |sorted|;
  for i := 1 to n - 1
    invariant 0 <= i <= n
    invariant |sorted| == n
    invariant multiset(s) == multiset(sorted)
    invariant is_sorted_by_key(sorted[0..i], key)
    invariant forall k :: i <= k < n ==> s[k] == sorted[k]
  {
    var j := i;
    while j > 0 && key(sorted[j-1]) > key(sorted[j])
      invariant 0 <= j <= i
      invariant |sorted| == n
      invariant multiset(s) == multiset(sorted)
      invariant sorted[0..j] == old(sorted)[0..j]
      invariant sorted[j+1..i+1] == old(sorted)[j+1..i+1]
      invariant forall k :: i < k < n ==> s[k] == sorted[k]
      invariant is_sorted_by_key(sorted[0..j-1], key)
      invariant is_sorted_by_key(sorted[j+1..i+1], key)
      invariant forall k :: 0 <= k < j-1 ==> key(sorted[k]) <= key(sorted[j-1])
      invariant forall k :: j+1 <= k < i+1 ==> key(sorted[j]) <= key(sorted[k])
      invariant key(sorted[j]) < key(sorted[j-1])
    {
      var temp := sorted[j];
      sorted[j] := sorted[j-1];
      sorted[j-1] := temp;
      j := j - 1;
    }
  }
}
// </vc-code>

