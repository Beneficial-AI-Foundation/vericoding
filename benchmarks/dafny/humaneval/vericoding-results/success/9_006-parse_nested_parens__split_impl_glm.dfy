// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function isParen(c: char): bool { c == '(' || c == ')' }
function isSpace(c: char): bool { c == ' ' }
/* helper modified by LLM (iteration 2): Added isNonEmptyParentheses predicate */
predicate isNonEmptyParentheses(s: string) { |s| > 0 && forall i :: 0 <= i < |s| ==> isParen(s[i]) }
// </vc-helpers>

// <vc-spec>
method split(s : string) returns (res : seq<string>)

    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '

    ensures forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed implementation to use defined helpers */
{
  var i := 0;
  var current := "";
  res := [];
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant (forall j :: 0 <= j < |res| ==> isNonEmptyParentheses(res[j]))
    invariant isNonEmptyParentheses(current) || current == ""
  {
    if isSpace(s[i]) {
      if current != "" {
        res := res + [current];
        current := "";
      }
    } else {
      current := current + [s[i]];
    }
    i := i + 1;
  }
  
  if current != "" {
    res := res + [current];
  }
}
// </vc-code>
