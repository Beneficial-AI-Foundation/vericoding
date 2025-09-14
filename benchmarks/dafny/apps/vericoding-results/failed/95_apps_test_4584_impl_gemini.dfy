predicate ValidInput(n: int, aa: seq<int>)
{
    n >= 2 &&
    |aa| == n - 1 &&
    forall i :: 0 <= i < |aa| ==> 1 <= aa[i] < i + 2
}

function SubordinateCount(aa: seq<int>, boss_id: int): int
{
    |set j | 0 <= j < |aa| && aa[j] == boss_id|
}

predicate ValidOutput(n: int, aa: seq<int>, result: seq<int>)
{
    |result| == n &&
    forall i :: 0 <= i < n ==> result[i] >= 0 &&
    forall i :: 0 <= i < n ==> result[i] == SubordinateCount(aa, i + 1)
}

// <vc-helpers>
lemma SubordinateCountAppend(s: seq<int>, x: int, v: int)
  ensures SubordinateCount(s + [x], v) == SubordinateCount(s, v) + (if x == v then 1 else 0)
{
  var s_prime := s + [x];
  var set_s_prime
// </vc-helpers>

// <vc-spec>
method solve(n: int, aa: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, aa)
    ensures ValidOutput(n, aa, result)
// </vc-spec>
// <vc-code>
lemma SubordinateCountAppend(s: seq<int>, x: int, v: int)
  ensures SubordinateCount(s + [x], v) == SubordinateCount(s, v) + (if x == v then 1 else 0)
{
  var s_prime := s + [x];
  var set_s_prime
// </vc-code>

