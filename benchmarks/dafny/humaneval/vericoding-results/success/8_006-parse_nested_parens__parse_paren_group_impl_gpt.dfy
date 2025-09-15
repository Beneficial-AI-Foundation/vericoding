// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function imax(a: int, b: int): int { if a >= b then a else b }
predicate IsParen(c: char) { c == '(' || c == ')' }
function nextDepth(d: int, c: char): int { if c == '(' then d + 1 else d - 1 }
// </vc-helpers>

// <vc-spec>
method parse_paren_group(s : string) returns (max_depth : int)

    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'

    ensures max_depth >= 0
// </vc-spec>
// <vc-code>
{
  var depth := 0;
  max_depth := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant max_depth >= 0
    invariant depth <= max_depth
    decreases |s| - i
  {
    var ch := s[i];
    depth := nextDepth(depth, ch);
    if depth > max_depth {
      max_depth := depth;
    }
    i := i + 1;
  }
}
// </vc-code>
