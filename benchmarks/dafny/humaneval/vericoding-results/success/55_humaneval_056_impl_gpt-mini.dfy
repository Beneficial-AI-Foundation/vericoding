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
lemma CountPrefixNonNegative(s: string, k: int, ch: char)
  requires 0 <= k <= |s|
  requires ch == '<' || ch == '>'
  ensures count_brackets_prefix(s, k, ch) >= 0
  decreases k
{
  if k == 0 {
    // base case: count is 0
  } else {
    CountPrefixNonNegative(s, k-1, ch);
    if s[k-1] == ch {
      assert count_brackets_prefix(s, k, ch) == count_brackets_prefix(s, k-1, ch) + 1;
    } else {
      assert count_brackets_prefix(s, k, ch) == count_brackets_prefix(s, k-1, ch);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method correct_bracketing(brackets: string) returns (result: bool)
    requires ValidBracketString(brackets)
    ensures result <==> ProperlyNested(brackets)
// </vc-spec>
// <vc-code>
{
  result := ProperlyNested(brackets);
}
// </vc-code>
