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
function count_depth(s: string, index: int): int
  requires 0 <= index <= |s|
  requires forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')'
  decreases |s| - index
{
  if index == |s| then 0
  else
    var curr := if s[index] == '(' then 1 else -1;
    var next_depth := count_depth(s, index + 1);
    curr + next_depth
}

function max_depth_helper(s: string, index: int, current_depth: int, max_so_far: int): int
  requires 0 <= index <= |s|
  requires current_depth >= 0
  requires max_so_far >= 0
  requires forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')'
  decreases |s| - index
{
  if index == |s| then max_so_far
  else
    var new_depth := current_depth + (if s[index] == '(' then 1 else -1);
    var new_max := if new_depth > max_so_far then new_depth else max_so_far;
    if new_depth < 0 then max_depth_helper(s, index + 1, 0, new_max)
    else max_depth_helper(s, index + 1, new_depth, new_max)
}

lemma MaxDepthNonNegative(s: string, index: int, current_depth: int, max_so_far: int)
  requires 0 <= index <= |s|
  requires current_depth >= 0
  requires max_so_far >= 0
  requires forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')'
  ensures max_depth_helper(s, index, current_depth, max_so_far) >= 0
  decreases |s| - index
{
  if index == |s| {
    assert max_so_far >= 0;
  } else {
    var new_depth := current_depth + (if s[index] == '(' then 1 else -1);
    var new_max := if new_depth > max_so_far then new_depth else max_so_far;
    if new_depth < 0 {
      assert new_max >= max_so_far >= 0;
      MaxDepthNonNegative(s, index + 1, 0, new_max);
    } else {
      assert new_max >= 0;
      MaxDepthNonNegative(s, index + 1, new_depth, new_max);
    }
  }
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
method SplitString(s: string) returns (res: seq<string>)
  requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
  ensures forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
{
  res := [];
  var current := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall s1 :: s1 in res ==> (forall j :: 0 <= j < |s1| ==> s1[j] == '(' || s1[j] == ')') && |s1| > 0
    invariant forall j :: 0 <= j < |current| ==> current[j] == '(' || current[j] == ')'
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
  if |current| > 0 {
    res := res + [current];
  }
}

method ParseNestedParens(paren_string: string) returns (res: seq<int>)
  requires forall i :: i >= 0 && i < |paren_string| ==> paren_string[i] == '(' || paren_string[i] == ')' || paren_string[i] == ' '
  ensures forall x :: x in res ==> x >= 0
{
  var groups := SplitString(paren_string);
  res := [];
  var i := 0;
  while i < |groups|
    invariant 0 <= i <= |groups|
    invariant forall x :: x in res ==> x >= 0
  {
    var group := groups[i];
    var max_depth := max_depth_helper(group, 0, 0, 0);
    MaxDepthNonNegative(group, 0, 0, 0);
    res := res + [max_depth];
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