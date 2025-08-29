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
predicate valid_split_result(s: string, res: seq<string>)
{
    forall part :: part in res ==> |part| >= 0
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method split(s : string) returns (res : seq<string>)
Process input. Requires: the condition holds for all values. Ensures: the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method split(s : string) returns (res : seq<string>)
    requires |s| >= 0
    ensures forall part :: part in res ==> |part| >= 0
    ensures valid_split_result(s, res)
// </vc-spec>
// <vc-code>
{
    res := [];
    if |s| == 0 {
        return;
    }
    
    var current := "";
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |current| >= 0
        invariant forall part :: part in res ==> |part| >= 0
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