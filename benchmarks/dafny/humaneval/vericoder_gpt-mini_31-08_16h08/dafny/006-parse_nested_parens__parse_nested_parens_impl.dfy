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

// <vc-helpers>
// No helper code required for verification.
// </vc-helpers>

// <vc-spec>
method parse_nested_parens(paren_string: string) returns (res : seq<int>)
    // pre-conditions-start
    requires forall i :: i >= 0 && i < |paren_string| ==> paren_string[i] == '(' || paren_string[i] == ')' || paren_string[i] == ' '
    // pre-conditions-end
    // post-conditions-start
    ensures forall x :: x in res ==> x >= 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  res := [];
  var n := |paren_string|;
  var i := 0;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant forall x :: x in res ==> x >= 0
  {
    // skip spaces
    while i < n && paren_string[i] == ' '
      decreases n - i
      invariant 0 <= i <= n
    {
      i := i + 1;
    }
    if i >= n { break; }
    var start := i;
    // find end of token
    while i < n && paren_string[i] != ' '
      decreases n - i
      invariant 0 <= i <= n
      invariant start <= i <= n
      invariant forall k :: start <= k < i ==> paren_string[k] != ' '
    {
      i := i + 1;
    }
    // compute max depth for paren_string[start..i-1]
    var depth := 0;
    var maxd := 0;
    var j := start;
    while j < i
      decreases i - j
      invariant start <= j <= i
      invariant i <= n
      invariant forall k :: start <= k < i ==> paren_string[k] != ' '
    {
      assert j < n;
      assert paren_string[j] != ' ';
      if paren_string[j] == '(' {
        depth := depth + 1;
        if depth > maxd { maxd := depth; }
      } else {
        depth := depth - 1;
      }
      j := j + 1;
    }
    assert maxd >= 0;
    res := res + [maxd];
  }
}
// </vc-code>

