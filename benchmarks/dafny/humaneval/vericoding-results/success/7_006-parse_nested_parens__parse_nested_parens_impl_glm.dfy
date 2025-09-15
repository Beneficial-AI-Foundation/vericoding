// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function isOpenParen(c: char): bool { c == '(' }
function isCloseParen(c: char): bool { c == ')' }
function isSpace(c: char): bool { c == ' ' }
// </vc-helpers>

// <vc-spec>
method parse_nested_parens(paren_string: string) returns (res : seq<int>)

    requires forall i :: i >= 0 && i < |paren_string| ==> paren_string[i] == '(' || paren_string[i] == ')' || paren_string[i] == ' '

    ensures forall x :: x in res ==> x >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed loop invariant by conditionally adding in open paren branch */
{
  var nesting_level := 0;
  var result := [];
  
  for i := 0 to |paren_string|
    invariant forall x :: x in result ==> x >= 0
  {
    if isOpenParen(paren_string[i]) {
      nesting_level := nesting_level + 1;
      if nesting_level >= 0 {
        result := result + [nesting_level];
      }
    } else if isCloseParen(paren_string[i]) {
      if nesting_level >= 0 {
        result := result + [nesting_level];
      }
      nesting_level := nesting_level - 1;
    }
  }
  
  res := result;
}
// </vc-code>
