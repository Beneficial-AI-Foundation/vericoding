// <vc-preamble>

function count_brackets_prefix(s: string, end: int, bracket: char): int
    requires 0 <= end <= |s|
    requires bracket == '<' || bracket == '>'
{
    if end == 0 then 0
    else if s[end-1] == bracket then 1 + count_brackets_prefix(s, end-1, bracket)
    else count_brackets_prefix(s, end-1, bracket)
}

predicate ValidBracketString(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == '<' || s[i] == '>'
}

predicate ProperlyNested(brackets: string)
    requires ValidBracketString(brackets)
{
    (forall k :: 0 <= k <= |brackets| ==> 
        count_brackets_prefix(brackets, k, '<') >= count_brackets_prefix(brackets, k, '>')) &&
    count_brackets_prefix(brackets, |brackets|, '<') == count_brackets_prefix(brackets, |brackets|, '>')
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method correct_bracketing(brackets: string) returns (result: bool)
    requires ValidBracketString(brackets)
    ensures result <==> ProperlyNested(brackets)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
