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
predicate IsSortedByDigitsSum(a: seq<int>) {
  forall i, j :: 0 <= i < j < |a| ==> digits_sum(a[i]) <= digits_sum(a[j])
}

function Insert(a: seq<int>, x: int): (res: seq<int>)
  requires IsSortedByDigitsSum(a)
  ensures IsSortedByDigitsSum(res)
  ensures |res| == |a| + 1
  ensures multiset(res) == multiset(a) + multiset({x})
  decreases |a|
{
  if |a| == 0 then [x]
  else if digits_sum(x) <= digits_sum(a[0]) then [x] + a
  else [a[0]] + Insert(a[1..], x)
}
// </vc-helpers>

// <vc-spec>
method order_by_points(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> digits_sum(sorted[i]) <= digits_sum(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant IsSortedByDigitsSum(sorted)
    invariant |sorted| == i
    invariant multiset(s) == multiset(sorted) + multiset(s[i..])
  {
    sorted := Insert(sorted, s[i]);
    i := i + 1;
  }
}
// </vc-code>
