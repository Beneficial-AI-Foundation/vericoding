// <vc-preamble>
function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method order_by_points(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> digits_sum(sorted[i]) <= digits_sum(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant multiset(sorted) == multiset(s)
    invariant forall k, l :: 0 <= k < l < i ==> digits_sum(sorted[k]) <= digits_sum(sorted[l])
    invariant forall k :: 0 <= k < i ==> forall l :: i <= l < |sorted| ==> digits_sum(sorted[k]) <= digits_sum(sorted[l])
  {
    var minIdx := i;
    var j := i + 1;
    while j < |sorted|
      invariant i < j <= |sorted|
      invariant i <= minIdx < j
      invariant forall k :: i <= k < j ==> digits_sum(sorted[minIdx]) <= digits_sum(sorted[k])
    {
      if digits_sum(sorted[j]) < digits_sum(sorted[minIdx]) {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIdx]][minIdx := temp];
    }
    i := i + 1;
  }
}
// </vc-code>
