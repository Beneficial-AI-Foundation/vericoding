method parse_paren_group(s : string) returns (max_depth : int)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'
    // pre-conditions-end
    // post-conditions-start
    ensures max_depth >= 0
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function method max(a: int, b: int): int {
  if a > b then a else b
}

predicate balanced(s: string) {
  exists open, close :: |s| == open + close &&
    forall i :: 0 <= i < |s| ==> (if s[i] == '(' then 1 else -1) == (if i < open then 1 else -1) &&
    open == close
}
// </vc-helpers>

// <vc-spec>
method split(s : string) returns (res : seq<string>)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
    // pre-conditions-end
    // post-conditions-start
    ensures forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var current_depth := 0;
  max_depth := 0;
  
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant current_depth >= 0
    invariant max_depth >= 0
    invariant max_depth >= current_depth
  {
    if s[i] == '(' {
      current_depth := current_depth + 1;
      max_depth := max(max_depth, current_depth);
    } else {
      current_depth := current_depth - 1;
    }
    i := i + 1;
  }
}
// </vc-code>

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