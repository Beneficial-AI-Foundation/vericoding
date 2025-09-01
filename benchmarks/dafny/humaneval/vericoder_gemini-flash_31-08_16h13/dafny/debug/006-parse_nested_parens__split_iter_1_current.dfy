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
function is_paren(c: char): bool {
  c == '(' || c == ')'
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
  var res: seq<string> := [];
  var current_word: string := "";
  for i := 0 to |s|
    invariant res == old(res) + old(current_word)
    invariant current_word == old(current_word)[..]
    invariant forall x :: x in res ==> (forall i :: i >= 0 && i < |x| ==> is_paren(x[i])) && |x| > 0
    invariant forall i :: i >= 0 && i < |current_word| ==> is_paren(current_word[i])
  {
    if i < |s| && is_paren(s[i]) {
      current_word := current_word + s[i];
    } else {
      if |current_word| > 0 {
        res := res + [current_word];
      }
      current_word := "";
    }
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