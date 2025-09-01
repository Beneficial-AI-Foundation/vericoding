

// <vc-helpers>
function digits_sum_helper(x: int): int
  decreases abs_helper(x)
{
  if abs_helper(x) < 10 then x else x % 10 + digits_sum_helper(x / 10)
}
function abs_helper(x: int): int
  ensures abs_helper(x) >= 0
  ensures abs_helper(x) == x || abs_helper(x) == -x
{
  if x >= 0 then x else -x
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
  var current_cnt := 0; // Renamed 'cnt' to 'current_cnt' to avoid duplicate local-variable name.
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant current_cnt == |set k | 0 <= k < i && digits_sum_helper(s[k]) > 0|
  {
    if digits_sum_helper(s[i]) > 0 {
      current_cnt := current_cnt + 1;
    }
    i := i + 1;
  }
  return current_cnt;
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