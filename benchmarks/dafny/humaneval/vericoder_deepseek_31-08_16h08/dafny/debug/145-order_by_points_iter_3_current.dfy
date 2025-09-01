function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
lemma digits_sum_nonneg(n: int)
  ensures digits_sum(n) >= 0
{
  if n < 0 {
    assert digits_sum(n) == digits_sum_pos(-n);
    assert digits_sum_pos(-n) >= 0;
  } else {
    assert digits_sum(n) == digits_sum_pos(n);
    assert digits_sum_pos(n) >= 0;
  }
}

lemma digits_sum_pos_monotonic(a: int, b: int)
  requires 0 <= a <= b
  ensures digits_sum_pos(a) <= digits_sum_pos(b)
{
  if b < 10 {
    assert a == b;
  } else if a < 10 {
    assert digits_sum_pos(a) == a;
    assert digits_sum_pos(b) == digits_sum_pos(b / 10) + b % 10;
    assert digits_sum_pos(b) >= b % 10 >= 0;
    assert a <= b % 10 || a > b % 10;
  } else {
    digits_sum_pos_monotonic(a / 10, b / 10);
    assert a % 10 <= b % 10;
  }
}

lemma digits_sum_monotonic(a: int, b: int)
  requires a <= b
  ensures digits_sum(a) <= digits_sum(b)
{
  if a < 0 && b < 0 {
    assert digits_sum(a) == digits_sum_pos(-a);
    assert digits_sum(b) == digits_sum_pos(-b);
    assert -b <= -a;
    digits_sum_pos_monotonic(-b, -a);
  } else if a < 0 && b >= 0 {
    assert digits_sum(a) == digits_sum_pos(-a);
    digits_sum_nonneg(-a);
    digits_sum_nonneg(b);
  } else if a >= 0 && b >= 0 {
    digits_sum_pos_monotonic(a, b);
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
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant forall k, l :: 0 <= k < l < i ==> digits_sum(sorted[k]) <= digits_sum(sorted[l])
    invariant multiset(sorted) == multiset(s)
    invariant |sorted| == |s|
  {
    var j := i;
    var min_idx := j;
    while j < |sorted|
      invariant i <= j <= |sorted|
      invariant min_idx >= i
      invariant min_idx < |sorted|
      invariant forall k :: i <= k < j ==> digits_sum(sorted[min_idx]) <= digits_sum(sorted[k])
    {
      if digits_sum(sorted[j]) < digits_sum(sorted[min_idx]) {
        min_idx := j;
      } else if digits_sum(sorted[j]) == digits_sum(sorted[min_idx]) {
        // Maintain stability or just continue
      }
      j := j + 1;
    }
    if min_idx != i {
      var temp := sorted[i];
      sorted := sorted[0..i] + [sorted[min_idx]] + sorted[i+1..min_idx] + [temp] + sorted[min_idx+1..];
    }
    i := i + 1;
  }
}
// </vc-code>

