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
lemma StringSplitProperties(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    ensures |s[start..end]| == end - start
    ensures forall i :: 0 <= i < |s[start..end]| ==> s[start..end][i] == s[start + i]
{
}

lemma EmptyStringNotInResult(s: string, res: seq<string>)
    requires forall s1 :: s1 in res ==> |s1| > 0
    ensures "" !in res
{
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
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall s1 :: s1 in res ==> (forall j :: 0 <= j < |s1| ==> s1[j] == '(' || s1[j] == ')') && |s1| > 0
    {
        if s[i] == ' ' {
            i := i + 1;
        } else {
            var start := i;
            while i < |s| && s[i] != ' '
                invariant start <= i <= |s|
                invariant forall j :: start <= j < i ==> s[j] == '(' || s[j] == ')'
            {
                i := i + 1;
            }
            
            if start < i {
                var group := s[start..i];
                StringSplitProperties(s, start, i);
                assert |group| > 0;
                assert forall j :: 0 <= j < |group| ==> group[j] == '(' || group[j] == ')';
                res := res + [group];
            }
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