// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int {
  if a > b then a else b
}

/* helper modified by LLM (iteration 4): Fixed decreases clause for currentDepth */
function currentDepth(s: string, pos: int): int 
  requires 0 <= pos <= |s|
  decreases s, pos
{
  if pos == 0 then 0 
  else currentDepth(s, pos-1) + (if s[pos-1] == '(' then 1 else if s[pos-1] == ')' then -1 else 0)
}

function findMaxDepth(s: string, pos: int, current_max: int): int 
  requires 0 <= pos <= |s|
  requires current_max >= 0
  ensures findMaxDepth(s, pos, current_max) >= 0
  decreases |s| - pos
{
  if pos == |s| then current_max
  else 
    var new_depth := currentDepth(s, pos+1);
    var new_max := if new_depth > current_max then new_depth else current_max;
    findMaxDepth(s, pos+1, new_max)
}
// </vc-helpers>

// <vc-spec>
method parse_paren_group(s : string) returns (max_depth : int)

    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'

    ensures max_depth >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Using fixed helper functions */
  max_depth := findMaxDepth(s, 0, 0);
}
// </vc-code>
