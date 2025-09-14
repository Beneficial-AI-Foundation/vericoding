// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed function signature to name return value */
function updateDepth(depth: int, c: char): (res: int)
  requires depth >= 0
  ensures res >= 0
{
  if c == '(' then depth + 1
  else if c == ')' then if depth > 0 then depth - 1 else 0
  else depth
}
// </vc-helpers>

// <vc-spec>
method parse_nested_parens(paren_string: string) returns (res : seq<int>)

    requires forall i :: i >= 0 && i < |paren_string| ==> paren_string[i] == '(' || paren_string[i] == ')' || paren_string[i] == ' '

    ensures forall x :: x in res ==> x >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): logic is correct, awaiting helper fix */
  var i := 0;
  res := [];
  var depth := 0;
  while i < |paren_string|
    invariant 0 <= i <= |paren_string|
    invariant depth >= 0
    invariant |res| == i
    invariant forall k :: 0 <= k < |res| ==> res[k] >= 0
  {
    depth := updateDepth(depth, paren_string[i]);
    res := res + [depth];
    i := i + 1;
  }
}
// </vc-code>
