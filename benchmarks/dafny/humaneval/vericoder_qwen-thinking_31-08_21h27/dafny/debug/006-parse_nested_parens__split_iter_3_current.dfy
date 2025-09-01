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
lemma string_append_ok(s: string, c: char)
  requires (forall k :: 0 <= k < |s| ==> s[k] == '(' || s[k] == ')')
  requires c == '(' || c == ')'
  ensures (forall k :: 0 <= k < |s| + 1 ==> (if k < |s| then s[k] == '(' || s[k] == ')' else c == '(' || c == ')'))
{
}
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
  var res := Seq<string>();
  var current := "";
  for i := 0 to |s| - 1 {
    invariant forall j :: 0 <= j < |res| ==> |res[j]| > 0 && (forall k :: 0 <= k < |res[j]| ==> res[j][k] == '(' || res[j][k] == ')')
    invariant current == "" || (forall k :: 0 <= k < |current| ==> current[k] == '(' || current[k] == ')')
    if s[i] == ' ' {
      if current != "" {
        res := res ++ [current];
        current := "";
      }
    } else {
      current := current + s[i];
    }
  }
  if current != "" {
    res := res ++ [current];
  }
  return res;
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