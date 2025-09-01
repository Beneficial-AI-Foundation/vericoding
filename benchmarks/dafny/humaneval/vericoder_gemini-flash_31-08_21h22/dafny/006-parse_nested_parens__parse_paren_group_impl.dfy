

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method parse_paren_group(s : string) returns (max_depth : int)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'
    // pre-conditions-end
    // post-conditions-start
    ensures max_depth >= 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var current_depth := 0;
  var max_depth_so_far := 0;
  var i := 0;

  while i < |s| 
    invariant 0 <= i <= |s|
    invariant current_depth >= 0
    invariant max_depth_so_far >= 0
    invariant max_depth_so_far >= current_depth
    invariant (forall j :: 0 <= j < i ==> s[j] == '(' || s[j] == ')')
  {
    if s[i] == '(' {
      current_depth := current_depth + 1;
      if current_depth > max_depth_so_far {
        max_depth_so_far := current_depth;
      }
    } else if s[i] == ')' {
      // It is impossible to have current_depth < 0 because the problem statement guarantees
      // balanced parentheses if it is a valid input for other parse functions.
      // So current_depth will always be >= 0.
      if current_depth > 0 { // Added check to ensure current_depth doesn't go below 0
        current_depth := current_depth - 1;
      }
    }
    i := i + 1;
  }
  max_depth := max_depth_so_far;
}
// </vc-code>

method split(s : string) returns (res : seq<string>)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
    // pre-conditions-end
    // post-conditions-start
    ensures forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
    // post-conditions-end
{
  assume{:axiom} false;
}
method parse_nested_parens(paren_string: string) returns (res : seq<int>)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |paren_string| ==> paren_string[i] == '(' || paren_string[i] == ')' || paren_string[i] == ' '
    // pre-conditions-end
    // post-conditions-start
    ensures forall x :: x in res ==> x >= 0
    // post-conditions-end
{
  assume{:axiom} false;
}