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
/* helper modified by LLM (iteration 2): Added lemma to prove depth relationship with count_brackets_prefix */
lemma DepthCorrespondsToCounts(brackets: string, i: int, depth: int)
    requires ValidBracketString(brackets)
    requires 0 <= i <= |brackets|
    requires depth == count_brackets_prefix(brackets, i, '<') - count_brackets_prefix(brackets, i, '>')
    ensures depth < 0 ==> !ProperlyNested(brackets)
{
    if depth < 0 {
        assert count_brackets_prefix(brackets, i, '<') < count_brackets_prefix(brackets, i, '>');
        assert !(forall k :: 0 <= k <= |brackets| ==> 
            count_brackets_prefix(brackets, k, '<') >= count_brackets_prefix(brackets, k, '>'));
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
  /* code modified by LLM (iteration 2): Added lemma call to prove postcondition when returning false */
  var depth := 0;
  var i := 0;
  
  while i < |brackets|
    invariant 0 <= i <= |brackets|
    invariant depth == count_brackets_prefix(brackets, i, '<') - count_brackets_prefix(brackets, i, '>')
    invariant depth >= 0
    invariant forall k :: 0 <= k <= i ==> count_brackets_prefix(brackets, k, '<') >= count_brackets_prefix(brackets, k, '>')
  {
    if brackets[i] == '<' {
      depth := depth + 1;
    } else {
      depth := depth - 1;
      if depth < 0 {
        assert count_brackets_prefix(brackets, i+1, '<') - count_brackets_prefix(brackets, i+1, '>') == depth;
        DepthCorrespondsToCounts(brackets, i+1, depth);
        return false;
      }
    }
    i := i + 1;
  }
  
  result := (depth == 0);
}
// </vc-code>
