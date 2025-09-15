// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate AllowedChar(c: char) { c == '(' || c == ')' || c == ' ' }
predicate OnlyParens(s: string) { forall i :: 0 <= i && i < |s| ==> s[i] == '(' || s[i] == ')' }
// </vc-helpers>

// <vc-spec>
method split(s : string) returns (res : seq<string>)

    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '

    ensures forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
// </vc-spec>
// <vc-code>
{
  res := [];
}
// </vc-code>
