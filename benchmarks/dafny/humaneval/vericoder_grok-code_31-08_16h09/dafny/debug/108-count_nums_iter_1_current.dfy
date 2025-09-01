

// <vc-helpers>
// <vc-helpers>
lemma DigitsSumPositiveNonZero(x: int)
  requires x != 0
  ensures digits_sum(x) != 0
{
  if x > 0 {
    assert abs(x) == x;
    assert digits_sum(x) > 0;
  } else {
    assert abs(x) == -x;
  }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method count_nums(s: seq<int>) returns (cnt: nat)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && digits_sum(s[i]) > 0|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var cnt := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
    invariant 0 <= i <= |s|
    invariant cnt == |set j | 0 <= j < i && digits_sum(s[j]) > 0|
  {
    if digits_sum(s[i]) > 0 {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

function digits_sum(x: int): int
  decreases abs(x)
{
  if abs(x) < 10 then x else x % 10 + digits_sum(x / 10)
}
// pure-end
function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
{
  if x >= 0 then x else -x
}
// pure-end