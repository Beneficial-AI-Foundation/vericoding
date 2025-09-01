

// <vc-helpers>
function max(a: int, b: int): int {
    if a > b then a else b
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
    var current_depth := 0;
    max_depth := 0;

    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= current_depth
        invariant 0 <= max_depth
        invariant forall k :: 0 <= k < i ==> s[k] == '(' || s[k] == ')'
        invariant current_depth == (count_char(s, '(', i) - count_char(s, ')', i))
        invariant max_depth == calc_max_depth(s, i)
    {
        if s[i] == '(' {
            current_depth := current_depth + 1;
            max_depth := max(max_depth, current_depth);
        } else if s[i] == ')' {
            current_depth := current_depth - 1;
        }
        i := i + 1;
    }
}

function calc_max_depth(s: string, length: int): int
    requires 0 <= length <= |s|
    requires forall k :: 0 <= k < length ==> s[k] == '(' || s[k] == ')'
{
    if length == 0 then 0
    else
        var prev_max := calc_max_depth(s, length - 1);
        var prev_balance := count_char(s, '(', length - 1) - count_char(s, ')', length - 1);
        if s[length - 1] == '(' then max(prev_max, prev_balance + 1)
        else prev_max
}

function count_char(s: string, c: char, length: int): int
    requires 0 <= length <= |s|
    requires forall k :: 0 <= k < length ==> s[k] == '(' || s[k] == ')'
    ensures 0 <= count_char(s, c, length) <= length
{
    if length == 0 then 0
    else
        var count := count_char(s, c, length - 1);
        if s[length - 1] == c then count + 1
        else count
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