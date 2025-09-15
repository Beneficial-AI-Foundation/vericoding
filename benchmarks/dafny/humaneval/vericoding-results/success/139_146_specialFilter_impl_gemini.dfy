// <vc-preamble>
function first_digit(n: int): int
  requires n >= 0
  ensures 0 <= first_digit(n) < 10
{
  if n < 10 then n else first_digit(n / 10)
}
function last_digit(n: int): int
  requires n >= 0
  ensures 0 <= last_digit(n) < 10
  ensures last_digit(n) == n % 10
{
  n % 10
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): made predicate safe to evaluate on all integers */
predicate IsSpecial(x: int) {
  x > 10 && first_digit(x) % 2 == 1 && last_digit(x) % 2 == 1
}

// </vc-helpers>

// <vc-spec>
method specialFilter(s: seq<int>) returns (r: seq<int>)

  ensures forall i :: 0 <= i < |r| ==> r[i] > 10
  ensures forall x :: x in r ==> x in s
  ensures forall i :: 0 <= i < |r| ==> first_digit(r[i]) % 2 == 1 && last_digit(r[i]) % 2 == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added non-negative check and index-based invariants */
  r := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall y :: y in r ==> y in s
    invariant forall k :: 0 <= k < |r| ==> r[k] > 10
    invariant forall k :: 0 <= k < |r| ==> first_digit(r[k]) % 2 == 1 && last_digit(r[k]) % 2 == 1
  {
    var x := s[i];
    if x >= 0 && IsSpecial(x) {
      r := r + [x];
    }
    i := i + 1;
  }
}
// </vc-code>
