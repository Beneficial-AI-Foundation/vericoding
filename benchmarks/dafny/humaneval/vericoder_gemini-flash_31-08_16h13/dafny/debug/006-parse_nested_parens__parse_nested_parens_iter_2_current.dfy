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
function IsParenChar(c: char): bool
{
  c == '(' || c == ')'
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
  var res_list: seq<int> := [];
  var current_paren_group_start := 0;
  var i := 0;

  while i < |paren_string|
    invariant 0 <= i <= |paren_string|
    invariant forall k :: current_paren_group_start <= k < i ==> IsParenChar(paren_string[k]) || paren_string[k] == ' '
    invariant forall k :: 0 <= k < |res_list| ==> res_list[k] >= 0
  {
    if IsParenChar(paren_string[i])
    {
      i := i + 1;
    }
    else // paren_string[i] == ' '
    {
      if i > current_paren_group_start
      {
        var group_str := paren_string[current_paren_group_start..i];
        // The precondition of parse_paren_group is:
        // requires forall j :: j >= 0 && j < |s| ==> s[j] == '(' || s[j] == ')'
        // We know that chars from current_paren_group_start to i-1 are '(' or ')'.
        // So, this call is valid.
        res_list := res_list + [parse_paren_group(group_str)];
      }
      i := i + 1;
      current_paren_group_start := i; // Start a new group after the space
    }
  }

  if i > current_paren_group_start
  {
    var group_str := paren_string[current_paren_group_start..i];
    res_list := res_list + [parse_paren_group(group_str)];
  }

  return res_list;
}
// </vc-code>

