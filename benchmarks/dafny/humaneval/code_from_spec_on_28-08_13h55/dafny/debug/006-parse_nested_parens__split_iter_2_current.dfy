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
predicate is_valid_paren_group(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')'
}

predicate is_space(c: char)
{
    c == ' '
}

function split_by_space(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then
        []
    else if s[0] == ' ' then
        split_by_space(s[1..])
    else
        var end := find_next_space_or_end(s, 0);
        [s[0..end]] + split_by_space(s[end..])
}

function find_next_space_or_end(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= find_next_space_or_end(s, start) <= |s|
    decreases |s| - start
{
    if start >= |s| then |s|
    else if s[start] == ' ' then start
    else find_next_space_or_end(s, start + 1)
}

lemma split_preserves_valid_groups(s: string)
    requires forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
    ensures forall group :: group in split_by_space(s) ==> is_valid_paren_group(group)
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method split(s : string) returns (res : seq<string>)
Process input. Requires: the condition holds for all values. Ensures: the condition holds for all values.
*/
// </vc-description>

// <vc-code>
method split(s : string) returns (res : seq<string>)
    requires forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
    ensures forall group :: group in res ==> is_valid_paren_group(group)
    ensures forall group :: group in res ==> |group| > 0
{
    res := [];
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall group :: group in res ==> is_valid_paren_group(group)
        invariant forall group :: group in res ==> |group| > 0
    {
        if s[i] == ' ' {
            i := i + 1;
        } else {
            var start := i;
            while i < |s| && s[i] != ' '
                invariant start <= i <= |s|
                invariant start < |s|
                invariant s[start] != ' '
                invariant forall j :: start <= j < i ==> s[j] != ' '
            {
                i := i + 1;
            }
            var group := s[start..i];
            assert |group| > 0;
            assert forall j :: 0 <= j < |group| ==> j + start < |s|;
            assert forall j :: 0 <= j < |group| ==> group[j] == s[j + start];
            assert forall j :: start <= j < i ==> s[j] != ' ';
            assert forall j :: 0 <= j < |group| ==> s[j + start] == '(' || s[j + start] == ')';
            assert forall j :: 0 <= j < |group| ==> group[j] == '(' || group[j] == ')';
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