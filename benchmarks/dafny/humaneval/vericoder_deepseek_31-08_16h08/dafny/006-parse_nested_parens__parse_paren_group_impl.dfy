

// <vc-helpers>
function countMaxDepth(s: string, start: int, end: int) : (max_depth: int, current: int)
  requires 0 <= start <= end <= |s|
  requires forall i :: start <= i < end ==> s[i] == '(' || s[i] == ')'
  ensures max_depth >= 0
  decreases end - start
{
  if start >= end then
    (0, 0)
  else if s[start] == '(' then
    var (sub_max, sub_current) := countMaxDepth(s, start + 1, end);
    var new_current := sub_current + 1;
    (if new_current > sub_max then new_current else sub_max, new_current)
  else 
    var (sub_max, sub_current) := countMaxDepth(s, start + 1, end);
    if sub_current > 0 then
      (sub_max, sub_current - 1)
    else
      (sub_max, 0)
}

lemma countMaxDepthNonNegative(s: string, start: int, end: int)
  requires 0 <= start <= end <= |s|
  requires forall i :: start <= i < end ==> s[i] == '(' || s[i] == ')'
  ensures var (max_depth, current) := countMaxDepth(s, start, end); max_depth >= 0
  decreases end - start
{
  if start < end {
    if s[start] == '(' {
      countMaxDepthNonNegative(s, start + 1, end);
    } else {
      countMaxDepthNonNegative(s, start + 1, end);
    }
  }
}
// </vc-helpers>
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
  var (max_depth_result, _) := countMaxDepth(s, 0, |s|);
  countMaxDepthNonNegative(s, 0, |s|);
  max_depth := max_depth_result;
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