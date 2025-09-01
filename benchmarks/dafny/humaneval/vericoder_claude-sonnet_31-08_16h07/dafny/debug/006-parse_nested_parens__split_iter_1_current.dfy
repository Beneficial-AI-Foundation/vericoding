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
lemma StringSplitProperties(s: string, res: seq<string>)
    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
    requires forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
    ensures forall s1 :: s1 in res ==> forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')'
{
}

function method IsSpace(c: char): bool
{
    c == ' '
}

function method IsValidParenChar(c: char): bool
{
    c == '(' || c == ')'
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
{
    res := [];
    var i := 0;
    var start := 0;
    
    while i <= |s|
        invariant 0 <= i <= |s|
        invariant 0 <= start <= i
        invariant forall s1 :: s1 in res ==> (forall j :: j >= 0 && j < |s1| ==> s1[j] == '(' || s1[j] == ')') && |s1| > 0
    {
        if i == |s| || s[i] == ' ' {
            if start < i {
                var group := s[start..i];
                if |group| > 0 {
                    res := res + [group];
                }
            }
            start := i + 1;
        }
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