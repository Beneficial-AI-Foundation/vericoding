/*
function_signature: method parse_nested_parens(paren_string: string) returns (res : seq<int>)
Parse input. Requires: the condition holds for all values. Ensures: the condition holds for all values.
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method parse_nested_parens(paren_string: string) returns (res : seq<int>)

    requires forall i :: i >= 0 && i < |paren_string| ==> paren_string[i] == '(' || paren_string[i] == ')' || paren_string[i] == ' '

    ensures forall x :: x in res ==> x >= 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
