

// <vc-helpers>
function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
{
  if x >= 0 then x else -x
}

function digits_sum(x: int): int
  decreases abs(x)
  ensures digits_sum(x) >= 0
{
  let abs_x = abs(x);
  if abs_x < 10 then abs_x else abs_x % 10 + digits_sum(abs_x / 10)
}
// </vc-helpers>

// <vc-spec>
method count_nums(s: seq<int>) returns (cnt: nat)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && digits_sum(s[i]) > 0|
  // post-conditions-end
// </vc-spec>
// <vc-code>
return |{ i | 0 <= i && i < |s| && digits_sum(s[i]) > 0 }|
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