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
  var result: seq<string> := [];
  var current_word: string := "";
  for i := 0 to |s|
    invariant forall x :: x in result ==> (forall k :: k >= 0 && k < |x| ==> is_paren(x[k])) && |x| > 0
    invariant forall k :: k >= 0 && k < |current_word| ==> is_paren(current_word[k])
    invariant i <= |s|
  {
    if i < |s| && is_paren(s[i]) {
      current_word := current_word + [s[i]]; // char can be directly appended to string
    } else {
      if |current_word| > 0 {
        result := result + [current_word];
      }
      current_word := "";
    }
  }
  return result;
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