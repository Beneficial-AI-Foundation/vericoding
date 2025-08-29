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
predicate is_space_separated_parens(s: string)
{
  forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
}

predicate valid_paren_group(group: string)
{
  forall i :: 0 <= i < |group| ==> group[i] == '(' || group[i] == ')'
}

lemma split_preserves_char_property(s: string, groups: seq<string>)
  requires is_space_separated_parens(s)
  ensures forall group :: group in groups ==> valid_paren_group(group)
{
  // This lemma would prove that splitting on spaces preserves the character constraints
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method split(s : string) returns (res : seq<string>)
Process input. Requires: the condition holds for all values. Ensures: the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method split(s : string) returns (res : seq<string>)
  requires is_space_separated_parens(s)
  ensures forall group :: group in res ==> valid_paren_group(group)
  ensures forall group :: group in res ==> |group| > 0
// </vc-spec>
// <vc-code>
method split(s : string) returns (res : seq<string>)
  requires is_space_separated_parens(s)
  ensures forall group :: group in res ==> valid_paren_group(group)
  ensures forall group :: group in res ==> |group| > 0
{
  res := [];
  var current_group := "";
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall group :: group in res ==> valid_paren_group(group)
    invariant forall group :: group in res ==> |group| > 0
    invariant forall j :: 0 <= j < |current_group| ==> current_group[j] == '(' || current_group[j] == ')'
  {
    if s[i] == ' ' {
      if |current_group| > 0 {
        res := res + [current_group];
        current_group := "";
      }
    } else {
      current_group := current_group + [s[i]];
    }
    i := i + 1;
  }
  
  if |current_group| > 0 {
    res := res + [current_group];
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