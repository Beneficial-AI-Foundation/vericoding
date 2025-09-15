// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function containsOnlyParens(s: string): bool {
  forall i | 0 <= i < |s| :: s[i] == '(' || s[i] == ')'
}
predicate IsParenOrSpace(c: char) { c == '(' || c == ')' || c == ' ' }
// </vc-helpers>

// <vc-spec>
method split(s : string) returns (res : seq<string>)

    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '

    ensures forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
// </vc-spec>
// <vc-code>
{
  var current := "";
  res := [];
  var i := 0;
  
  while i < |s|
    invariant i <= |s|
    invariant forall s1 :: s1 in res ==> containsOnlyParens(s1) && |s1| > 0
    invariant |current| == 0 || containsOnlyParens(current)
  {
    if s[i] != ' ' {
      current := current + [s[i]];
    } else {
      if |current| > 0 {
        res := res + [current];
        current := "";
      }
    }
    i := i + 1;
  }
  
  if |current| > 0 {
    res := res + [current];
  }
}
// </vc-code>
