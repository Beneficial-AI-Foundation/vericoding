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
    var i: int := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < |res| ==> (forall c :: 0 <= c < |res[k]| ==> res[k][c]=='(' || res[k][c]==')') && |res[k]|>0
    {
        if s[i] == ' ' {
            i := i + 1;
        } else {
            var j: int := i;
            while j < |s| && s[j] != ' '
                invariant i <= j <= |s|
                invariant forall k :: i <= k < j ==> s[k] != ' '
            {
                j := j + 1;
            }
            assert j > i;
            var token := s[i..j];
            res := res + [token];
            i := j;
        }
    }
    return res;
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