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
predicate valid_char(c: char) {
    c == '(' || c == ')'
}

predicate valid_paren_string(s: string) {
    forall i :: 0 <= i < |s| ==> valid_char(s[i])
}

lemma substring_preserves_valid_chars(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    requires forall i :: 0 <= i < |s| ==> (s[i] == '(' || s[i] == ')' || s[i] == ' ')
    ensures forall i :: 0 <= i < end - start ==> (s[start + i] == '(' || s[start + i] == ')' || s[start + i] == ' ')
{
}

lemma substring_valid_parens(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> (s[i] == '(' || s[i] == ')')
    ensures forall i :: 0 <= i < end - start ==> (s[start..end][i] == '(' || s[start..end][i] == ')')
{
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
            
            if i > start {
                var segment := s[start..i];
                substring_valid_parens(s, start, i);
                res := res + [segment];
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