// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a > b then a else b }
// </vc-helpers>

// <vc-spec>
method parse_paren_group(s : string) returns (max_depth : int)

    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'

    ensures max_depth >= 0
// </vc-spec>
// <vc-code>
{
  max_depth := 0;
  var current_depth := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant max_depth >= 0
    decreases |s| - i
  {
    if s[i] == '(' {
      current_depth := current_depth + 1;
      max_depth := max(max_depth, current_depth);
    } else {
      current_depth := current_depth - 1;
    }
    i := i + 1;
  }
}
// </vc-code>
