// <vc-preamble>

predicate valid_paren_string(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')'
}

function is_balanced_helper(s: string, depth: int): int
{
    if |s| == 0 then depth
    else if s[0] == '(' then is_balanced_helper(s[1..], depth + 1)
    else if s[0] == ')' then 
        if depth > 0 then is_balanced_helper(s[1..], depth - 1)
        else -1
    else is_balanced_helper(s[1..], depth)
}

function is_balanced(s: string): bool
{
    is_balanced_helper(s, 0) == 0
}

predicate ValidInput(lst: seq<string>)
{
    |lst| == 2 && valid_paren_string(lst[0]) && valid_paren_string(lst[1])
}

predicate CorrectOutput(lst: seq<string>, result: string)
    requires ValidInput(lst)
{
    (result == "Yes" || result == "No") &&
    (result == "Yes" <==> (is_balanced(lst[0] + lst[1]) || is_balanced(lst[1] + lst[0])))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method match_parens(lst: seq<string>) returns (result: string)
    requires ValidInput(lst)
    ensures CorrectOutput(lst, result)
// </vc-spec>
// <vc-code>
{
  var concat1 := lst[0] + lst[1];
  var concat2 := lst[1] + lst[0];
  
  if is_balanced(concat1) || is_balanced(concat2) {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>
