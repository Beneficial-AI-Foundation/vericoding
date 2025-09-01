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

function IsSpace(c: char): bool
{
    c == ' '
}

function IsValidParenChar(c: char): bool
{
    c == '(' || c == ')'
}

lemma SubstringPreservesParenProperty(s: string, start: int, end: int)
    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
    requires 0 <= start <= end <= |s|
    ensures forall i :: i >= 0 && i < |s[start..end]| ==> s[start..end][i] == '(' || s[start..end][i] == ')'
{
    var substring := s[start..end];
    forall i | 0 <= i < |substring|
        ensures substring[i] == '(' || substring[i] == ')'
    {
        assert substring[i] == s[start + i];
        assert start + i >= 0 && start + i < |s|;
        assert s[start + i] == '(' || s[start + i] == ')' || s[start + i] == ' ';
        assert substring[i] != ' ';
    }
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
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= start <= |s|
        invariant forall s1 :: s1 in res ==> (forall j :: j >= 0 && j < |s1| ==> s1[j] == '(' || s1[j] == ')') && |s1| > 0
    {
        if s[i] == ' ' {
            if start < i {
                var group := s[start..i];
                if |group| > 0 {
                    SubstringPreservesParenProperty(s, start, i);
                    res := res + [group];
                }
            }
            start := i + 1;
        }
        i := i + 1;
    }
    
    if start < |s| {
        var group := s[start..|s|];
        if |group| > 0 {
            SubstringPreservesParenProperty(s, start, |s|);
            res := res + [group];
        }
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