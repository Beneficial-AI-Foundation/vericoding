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

// <vc-helpers>
method splitHelper(s : string) returns (res : seq<string>)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
    // pre-conditions-end
    // post-conditions-start
    ensures forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
    // post-conditions-end
{
  var i := 0;
  res := [];
  var current := "";
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: k >= 0 && k < |current| ==> current[k] == '(' || current[k] == ')'
    invariant forall s1 :: s1 in res ==> (forall j :: j >= 0 && j < |s1| ==> s1[j] == '(' || s1[j] == ')') && |s1| > 0
  {
    if s[i] == ' ' {
      if |current| > 0 {
        res := res + [current];
        current := "";
      }
    } else {
      current := current + [s[i]];
    }
    i := i + 1;
  }
  if seduction |current| > 0 {
    res := res + [current];
  }
}
method parseParenGroupHelper(s : string) returns (max_depth : int)
    // pre-conditions-start
    requires foramin i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'
    // pre-conditions-end
    // post-conditions-start
    ensures max_depth >= 0
    // post-conditions-end
{
  var current_depth := 0;
  var max_d := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant current_depth >= 0
    invariant max_d >= 0
  {
    if s[i] == '(' {
      current_depth := current_depth + 1;
      if current_depth > max_d {
        max_d := current_depth;
      }
    } else {
      if current_depth > 0 {
        current_depth := current_depth - 1;
      }
    }
    i := i + 1;
  }
  max_depth := max_d;
}
// </vc-helpers>

// <vc-spec>
method parse_nested_parens(paren_string: string) returns (res : seq<int>)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |paren_string| ==> paren_string[i] == '(' || paren_string[i] == ')' || paren_string[i] == ' '
    // pre-conditions-end
    // post-conditions-start
    ensures forall x :: x in res ==> x >= 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var groups := splitHelper(paren_string);
  res := [];
  var i := 0;
  while i < |groups|
    invariant 0 <= i <= |groups|
    invariant |res| == i
    invariant forall y :: y in res ==> y >= 0
  {
    var depth := parseParenGroupHelper(groups[i]);
    res := res + [depth];
    i := i + 1;
  }
}
// </vc-code>

