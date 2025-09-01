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
function max(a: int, b: int): int {
  if a > b then a else b
}

function isBalanced(s: string, i: int, depth: int): bool 
  decreases |s| - i
{
  if i >= |s| then depth == 0
  else if s[i] == '(' then isBalanced(s, i+1, depth+1)
  else if s[i] == ')' && depth > 0 then isBalanced(s, i+1, depth-1)
  else false
}

function calculateMaxDepth(s: string, i: int, current: int, max_so_far: int): int 
  decreases |s| - i
  requires 0 <= i <= |s|
  ensures calculateMaxDepth(s, i, current, max_so_far) >= max_so_far
{
  if i >= |s| then max_so_far
  else if s[i] == '(' then 
    let new_current := current + 1;
    let new_max := max(new_current, max_so_far);
    calculateMaxDepth(s, i+1, new_current, new_max)
  else if s[i] == ')' then
    calculateMaxDepth(s, i+1, current - 1, max_so_far)
  else
    calculateMaxDepth(s, i+1, current, max_so_far)
}

lemma {:induction false} calculateMaxDepth_valid(s: string, i: int, current: int, max_so_far: int)
  requires 0 <= i <= |s|
  requires forall j :: j >= 0 && j < |s| ==> s[j] == '(' || s[j] == ')'
  requires isBalanced(s, i, current)
  ensures calculateMaxDepth(s, i, current, max_so_far) >= max_so_far
{
  if i < |s| {
    if s[i] == '(' {
      var new_current := current + 1;
      var new_max := max(new_current, max_so_far);
      calculateMaxDepth_valid(s, i+1, new_current, new_max);
    } else if s[i] == ')' {
      calculateMaxDepth_valid(s, i+1, current - 1, max_so_far);
    }
  }
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
  var parts := split(paren_string);
  res := [];
  var idx := 0;
  
  while idx < |parts|
    invariant forall x :: x in res ==> x >= 0
    invariant idx >= 0
  {
    var s := parts[idx];
    var depth := 0;
    if |s| > 0 && isBalanced(s, 0, 0) {
      depth := calculateMaxDepth(s, 0, 0, 0);
    }
    res := res + [depth];
    idx := idx + 1;
  }
}
// </vc-code>

