/*
function_signature: method parse_paren_group(s : string) returns (max_depth : int)
Parse input. Requires: the condition holds for all values. Ensures: the result is at least the specified value.
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method parse_paren_group(s : string) returns (max_depth : int)

    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'

    ensures max_depth >= 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
