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
  var n := |s|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: k >= 0 && k < |res| ==>
                |res[k]| > 0 &&
                (forall t :: t >= 0 && t < |res[k]| ==> res[k][t] == '(' || res[k][t] == ')')
    decreases n - i
  {
    if s[i] == ' ' {
      i := i + 1;
      continue;
    }
    var j := i + 1;
    while j < n && s[j] != ' '
      invariant i + 1 <= j <= n
      invariant forall t :: t >= i && t < j ==> s[t] != ' '
      decreases n - j
    {
      j := j + 1;
    }
    var piece := s[i..j];
    // prove piece is non-empty and contains only '(' or ')'
    assert |piece| == j - i;
    assert j - i > 0;
    assert forall u :: u >= 0 && u < |piece| ==> piece[u] == s[i + u];
    assert forall u :: u >= 0 && u < |piece| ==> s[i + u] != ' ';
    assert forall u :: u >= 0 && u < |piece| ==> piece[u] == '(' || piece[u] == ')';
    res := res + [piece];
    i := j;
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