

// <vc-helpers>
lemma digits_sum_positive_implies_nonzero(x: int)
  requires digits_sum(x) > 0
  ensures x != 0
{
  if x == 0 {
    assert digits_sum(0) == 0;
  }
}

lemma digits_sum_zero_implies_zero(x: int)
  requires x == 0
  ensures digits_sum(x) == 0
{
}

ghost predicate InSet(i: int, s: seq<int>)
  requires 0 <= i < |s|
{
  digits_sum(s[i]) > 0
}

ghost function CountInRange(s: seq<int>, i: int): int
  requires 0 <= i <= |s|
  ensures CountInRange(s, i) == |set j | 0 <= j < i && digits_sum(s[j]) > 0|
{
  if i == 0 then 0
  else {
    var prev := CountInRange(s, i-1);
    if digits_sum(s[i-1]) > 0 then prev + 1 else prev
  }
}

lemma CountInRangeMonotonic(s: seq<int>, i: int, j: int)
  requires 0 <= i <= j <= |s|
  ensures CountInRange(s, i) <= CountInRange(s, j)
{
}

lemma CountInRangeComplete(s: seq<int>)
  ensures CountInRange(s, |s|) == |set i | 0 <= i < |s| && digits_sum(s[i]) > 0|
{
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
  cnt := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant cnt == CountInRange(s, i)
  {
    if digits_sum(s[i]) > 0 {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  assert CountInRange(s, |s|) == |set i | 0 <= i < |s| && digits_sum(s[i]) > 0|;
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