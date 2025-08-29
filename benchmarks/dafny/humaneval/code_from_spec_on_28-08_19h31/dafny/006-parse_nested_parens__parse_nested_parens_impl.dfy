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
method parseParenGroup(s : string) returns (max_depth : int)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'
    // pre-conditions-end
    // post-conditions-start
    ensures max_depth >= 0
    // post-conditions-end
{
    max_depth := 0;
    var current_depth := 0;
    for i := 0 to |s|
        invariant 0 <= current_depth
        invariant max_depth >= current_depth
        invariant max_depth >= 0
    {
        if s[i] == '(' {
            current_depth := current_depth + 1;
            if current_depth > max_depth {
                max_depth := current_depth;
            }
        } else if s[i] == ')' {
            if current_depth > 0 {
                current_depth := current_depth - 1;
            }
        }
    }
}

method splitString(s : string) returns (res : seq<string>)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
    // pre-conditions-end
    // post-conditions-start
    ensures forall s1 :: s1 in res ==> (forall i :: 0 <= i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
    // post-conditions-end
{
    res := [];
    var current := "";
    for i := 0 to |s|
        invariant forall s1 :: s1 in res ==> (forall j :: 0 <= j < |s1| ==> s1[j] == '(' || s1[j] == ')') && |s1| > 0
        invariant forall j :: 0 <= j < |current| ==> current[j] == '(' || current[j] == ')'
    {
        if s[i] == ' ' {
            if |current| > 0 {
                res := res + [current];
                current := "";
            }
        } else {
            current := current + s[i..i+1];
        }
    }
    if |current| > 0 {
        res := res + [current];
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
    var groups := splitString(paren_string);
    res := [];
    for i := 0 to |groups|
        invariant forall x :: x in res ==> x >= 0
    {
        var depth := parseParenGroup(groups[i]);
        res := res + [depth];
    }
}
// </vc-code>
