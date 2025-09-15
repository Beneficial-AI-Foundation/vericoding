// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method parse_paren_group(s : string) returns (max_depth : int)

    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'

    ensures max_depth >= 0
// </vc-spec>
// <vc-code>
{
  var depth := 0;
  var max_d := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if s[i] == '(' {
      depth := depth + 1;
      if depth > max_d {
        max_d := depth;
      }
    } else {
      depth := depth - 1;
    }
    i := i + 1;
  }
  max_depth := max_d;
}
// </vc-code>
