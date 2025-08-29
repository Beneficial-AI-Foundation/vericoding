// <vc-helpers>
// Helper function to compute the maximum depth of nested parentheses in a string
function maxDepth(s: string, i: int, currentDepth: int, maxSoFar: int): int
  requires 0 <= i <= |s|
  requires currentDepth >= 0
  decreases |s| - i
{
  if i == |s| then maxSoFar
  else if s[i] == '(' then maxDepth(s, i + 1, currentDepth + 1, if currentDepth + 1 > maxSoFar then currentDepth + 1 else maxSoFar)
  else if s[i] == ')' then maxDepth(s, i + 1, if currentDepth > 0 then currentDepth - 1 else 0, maxSoFar)
  else maxDepth(s, i + 1, currentDepth, maxSoFar)
}

// Helper function to track maximum depth up to index i
function maxDepthUpTo(s: string, i: int): int
  requires 0 <= i <= |s|
  decreases i
{
  if i == 0 then 0
  else
    var prevDepth := maxDepthUpTo(s, i - 1);
    var newDepth := if s[i-1] == '(' then prevDepth + 1
                    else if s[i-1] == ')' && prevDepth > 0 then prevDepth - 1
                    else prevDepth;
    if newDepth > prevDepth then newDepth else prevDepth
}

// Lemma to relate maxDepth and maxDepthUpTo
lemma MaxDepthRelation(s: string, i: int, currentDepth: int, maxSoFar: int)
  requires 0 <= i <= |s|
  requires currentDepth >= 0
  ensures maxDepth(s, i, currentDepth, maxSoFar) >= maxDepthUpTo(s, i)
  decreases |s| - i
{
  if i == |s| {
    assert maxDepthUpTo(s, i) == maxDepthUpTo(s, i);
  } else {
    if s[i] == '(' {
      MaxDepthRelation(s, i + 1, currentDepth + 1, if currentDepth + 1 > maxSoFar then currentDepth + 1 else maxSoFar);
    } else if s[i] == ')' {
      MaxDepthRelation(s, i + 1, if currentDepth > 0 then currentDepth - 1 else 0, maxSoFar);
    } else {
      MaxDepthRelation(s, i + 1, currentDepth, maxSoFar);
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method parse_paren_group(s : string) returns (max_depth : int)
Parse input. Requires: the condition holds for all values. Ensures: the result is at least the specified value.
*/
// </vc-description>

// <vc-spec>
method parse_paren_group(s: string) returns (max_depth: int)
  requires true
  ensures max_depth >= 0
  ensures max_depth == maxDepth(s, 0, 0, 0)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var currentDepth := 0;
  var maxSoFar := 0;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant currentDepth >= 0
    invariant maxSoFar >= 0
    invariant currentDepth == maxDepthUpTo(s, i)
    invariant maxSoFar >= maxDepthUpTo(s, i)
  {
    if s[i] == '(' {
      currentDepth := currentDepth + 1;
      if currentDepth > maxSoFar {
        maxSoFar := currentDepth;
      }
    } else if s[i] == ')' {
      if currentDepth > 0 {
        currentDepth := currentDepth - 1;
      }
    }
    i := i + 1;
  }
  max_depth := maxSoFar;
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