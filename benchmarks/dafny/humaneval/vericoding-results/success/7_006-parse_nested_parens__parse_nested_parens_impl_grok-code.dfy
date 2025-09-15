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
  /* code modified by LLM (iteration 4): added loop invariants to ensure res elements are >=0 and all variables bounds are respected */
  res := [];
  var i := 0;
  while i < |paren_string|
    invariant 0 <= i <= |paren_string|
    invariant forall y :: 0 <= y < |res| ==> res[y] >= 0
  {
    if paren_string[i] == ' ' {
      i := i + 1;
    } else {
      // new group
      var depth := 0;
      var max_dep := 0;
      var j := i;
      while j < |paren_string| && paren_string[j] != ' '
        invariant 0 <= j <= |paren_string|
        invariant depth >= 0
        invariant max_dep >= 0
        invariant max_dep >= depth
      {
        if paren_string[j] == '(' {
          depth := depth + 1;
          if depth > max_dep {
            max_dep := depth;
          }
        } else if paren_string[j] == ')' {
          if depth > 0 {
            depth := depth - 1;
          }
        }
        j := j + 1;
      }
      // Ensure max_dep >=0 before appending (already invariant)
      res := res + [max_dep];
      i := j;
    }
  }
}
// </vc-code>
