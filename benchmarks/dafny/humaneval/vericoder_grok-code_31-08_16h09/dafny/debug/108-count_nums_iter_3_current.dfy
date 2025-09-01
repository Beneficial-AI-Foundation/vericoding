

// <vc-helpers>
function digits_sum_abs(x: nat): int
  decreases x
{
  if x < 10 then x else x % 10 + digits_sum_abs(x / 10)
}

function digits_sum(x: int): int
  decreases abs(x)
{
  if x == 0 then 0 else digits_sum_abs(abs(x))
}

lemma DigitsSumPositiveNonZero(x: int)
  requires x != 0
  ensures digits_sum(x) > 0
{
  var a := abs(x);
  assert a != 0;
  DigitsSumNonZero(a);
}

lemma DigitsSumNonZero(x: nat)
  requires x != 0
  ensures digits_sum_abs(x) > 0
{
}
// </vc-helpers>

// <vc-spec>
method count_nums(s: seq<int>) returns (cnt: nat)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && digits_sum(s[i]) > 0|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  cnt := 0;
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