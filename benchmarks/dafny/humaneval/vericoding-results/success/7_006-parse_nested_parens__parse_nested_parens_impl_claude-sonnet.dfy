// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method parse_nested_parens(paren_string: string) returns (res : seq<int>)

    requires forall i :: i >= 0 && i < |paren_string| ==> paren_string[i] == '(' || paren_string[i] == ')' || paren_string[i] == ' '

    ensures forall x :: x in res ==> x >= 0
// </vc-spec>
// <vc-code>
{
  res := [];
  var current_depth := 0;
  var max_depth := 0;
  
  var i := 0;
  while i < |paren_string|
    invariant 0 <= i <= |paren_string|
    invariant current_depth >= 0
    invariant max_depth >= 0
    invariant forall x :: x in res ==> x >= 0
  {
    if paren_string[i] == '(' {
      current_depth := current_depth + 1;
      if current_depth > max_depth {
        max_depth := current_depth;
      }
    } else if paren_string[i] == ')' {
      if current_depth > 0 {
        current_depth := current_depth - 1;
      }
      if current_depth == 0 {
        res := res + [max_depth];
        max_depth := 0;
      }
    }
    i := i + 1;
  }
}
// </vc-code>
