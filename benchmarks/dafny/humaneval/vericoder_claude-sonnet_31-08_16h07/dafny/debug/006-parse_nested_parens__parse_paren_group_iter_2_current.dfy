

// <vc-helpers>
lemma depth_non_negative(s: string, i: int, current_depth: int)
    requires forall j :: 0 <= j < |s| ==> s[j] == '(' || s[j] == ')'
    requires 0 <= i <= |s|
    requires current_depth >= 0
    ensures current_depth >= 0
{
}

lemma max_depth_invariant(s: string, i: int, current_depth: int, max_depth: int)
    requires forall j :: 0 <= j < |s| ==> s[j] == '(' || s[j] == ')'
    requires 0 <= i <= |s|
    requires current_depth >= 0
    requires max_depth >= current_depth
    ensures max_depth >= 0
{
}
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
    max_depth := 0;
    var current_depth := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant max_depth >= 0
    {
        if s[i] == '(' {
            current_depth := current_depth + 1;
            if current_depth > max_depth {
                max_depth := current_depth;
            }
        } else {
            current_depth := current_depth - 1;
            if current_depth < 0 {
                current_depth := 0;
            }
        }
        i := i + 1;
    }
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