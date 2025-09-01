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
method parse_paren_group(s : string) returns (max_depth : int)
    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'
    ensures max_depth >= 0
{
    var depth := 0;
    var max := 0;
    for i := 0 to |s| - 1 {
        if s[i] == '(' {
            depth := depth + 1;
            if depth > max {
                max := depth;
            }
        } else {
            depth := depth - 1;
        }
    }
    return max;
}

method split(s : string) returns (res : seq<string>)
    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
    ensures forall x :: x in res ==> (forall j :: j >= 0 && j < |x| ==> x[j] == '(' || x[j] == ')') && |x| > 0
{
    var parts := [];
    var current := "";
    for i := 0 to |s| - 1 {
        if s[i] == ' ' {
            if current != "" {
                parts := parts + [current];
                current := "";
            }
        } else {
            current := current + s[i];
        }
    }
    if current != "" {
        parts := parts + [current];
    }
    return parts;
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
return [parse_paren_group(part) | part in split(paren_string)];
// </vc-code>

