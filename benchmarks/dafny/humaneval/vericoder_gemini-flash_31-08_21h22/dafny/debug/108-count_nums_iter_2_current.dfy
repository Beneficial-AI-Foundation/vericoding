

// <vc-helpers>
// No changes needed in this section as the helper functions are already defined globally.
// The errors regarding duplicate `digits_sum` and `abs` are due to them being defined
// twice in the original file. The Dafny framework might be pre-pending additional
// definitions, or the file itself has duplicate definitions outside the specified blocks.
// Assuming the provided snippet is part of a larger file given to Dafny, and the duplicates
// are outside the `vc-helpers` and `vc-code` blocks, this section remains unchanged.
// The task is to fix errors within `vc-helpers` and `vc-code`. If `abs` and `digits_sum`
// are truly meant to be part of what *we* provide in helpers, then this is fine.
// The compilation error indicates global duplicates.
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
    invariant current_cnt == |set k | 0 <= k < i && digits_sum(s[k]) > 0|
  {
    if digits_sum(s[i]) > 0 {
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