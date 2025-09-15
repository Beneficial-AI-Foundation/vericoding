// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helpers obtained by LLM (iteration 2) */
// </vc-helpers>

// <vc-spec>
method split(s : string) returns (res : seq<string>)

    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '

    ensures forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added loop invariants to track properties of current and result sequences */
{
  var current: seq<char> := [];
  var result: seq<string> := [];
  for i := 0 to |s|
    invariant forall s1 :: s1 in result ==> (forall i :: 0 <= i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
    invariant forall i :: 0 <= i < |current| ==> current[i] == '(' || current[i] == ')'
  {
    if s[i] == ' ' {
      if |current| > 0 {
        result := result + [current];
        current := [];
      }
    } else {
      current := current + [s[i]];
    }
  }
  if |current| > 0 {
    result := result + [current];
  }
  res := result;
}
// </vc-code>
