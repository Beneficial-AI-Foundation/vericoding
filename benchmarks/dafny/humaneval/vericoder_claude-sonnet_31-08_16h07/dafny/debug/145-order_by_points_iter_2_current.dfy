function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
lemma digits_sum_stable(a: int, b: int)
  ensures digits_sum(a) == digits_sum(b) ==> digits_sum(a) <= digits_sum(b)
{
}

lemma sort_maintains_multiset<T>(s: seq<T>, sorted: seq<T>)
  requires |s| == |sorted|
  requires multiset(s) == multiset(sorted)
  ensures multiset(s) == multiset(sorted)
{
}

lemma swap_preserves_multiset<T>(s: seq<T>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures multiset(s) == multiset(s[i := s[j]][j := s[i]])
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
{
  if |s| == 0 {
    sorted := [];
    return;
  }
  
  sorted := s;
  
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant forall x, y :: 0 <= x < y < i ==> digits_sum(sorted[x]) <= digits_sum(sorted[y])
  {
    var j := i;
    while j > 0 && digits_sum(sorted[j-1]) > digits_sum(sorted[j])
      invariant 0 <= j <= i
      invariant |sorted| == |s|
      invariant multiset(s) == multiset(sorted)
      invariant forall x, y :: 0 <= x < y < i && (y < j || x >= j) ==> digits_sum(sorted[x]) <= digits_sum(sorted[y])
      invariant forall x :: j < x <= i ==> digits_sum(sorted[j]) <= digits_sum(sorted[x])
      invariant j > 0 ==> (forall x :: 0 <= x < j-1 ==> digits_sum(sorted[x]) <= digits_sum(sorted[j]))
    {
      swap_preserves_multiset(sorted, j-1, j);
      sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>

