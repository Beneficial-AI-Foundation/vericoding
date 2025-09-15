// <vc-preamble>
function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): boolean indicator to int */
function indicator(b: bool): int { if b then 1 else 0 }
// </vc-helpers>

// <vc-spec>
method count(a: seq<int>, x: int) returns (cnt: int)

  ensures cnt == |set i | 0 <= i < |a| && a[i] == x|
  ensures cnt == count_rec(a, x)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement counting with loop and ghost set; maintain invariants to match spec */
  var i := 0;
  var acc := 0;
  ghost var s: set<int> := {};
  while i < |a|
    invariant 0 <= i <= |a|
    invariant s == set j | 0 <= j < i && a[j] == x
    invariant acc == |s|
    invariant acc + count_rec(a[i..], x) == count_rec(a, x)
    decreases |a| - i
  {
    if a[i] == x {
      s := s + {i};
      acc := acc + 1;
    }
    i := i + 1;
  }
  cnt := acc;
}
// </vc-code>
