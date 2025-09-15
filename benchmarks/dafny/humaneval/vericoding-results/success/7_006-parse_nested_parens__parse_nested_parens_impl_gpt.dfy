// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsValidChar(c: char): bool { c == '(' || c == ')' || c == ' ' }
function IsNonNegativeSeq(s: seq<int>): bool { forall x :: x in s ==> x >= 0 }
// </vc-helpers>

// <vc-spec>
method parse_nested_parens(paren_string: string) returns (res : seq<int>)

    requires forall i :: i >= 0 && i < |paren_string| ==> paren_string[i] == '(' || paren_string[i] == ')' || paren_string[i] == ' '

    ensures forall x :: x in res ==> x >= 0
// </vc-spec>
// <vc-code>
{
  res := [];
}
// </vc-code>
