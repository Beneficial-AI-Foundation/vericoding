// <vc-helpers>
// Helper predicate to check if a string contains only parentheses
predicate IsParenthesesString(s: string) {
  forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')'
}

// Helper function to check balance up to a certain index
function BalanceUpTo(s: string, index: int): int
  requires 0 <= index <= |s|
  requires IsParenthesesString(s)
  decreases index
{
  if index == 0 then 0
  else if s[index-1] == '(' then BalanceUpTo(s, index-1) + 1
  else BalanceUpTo(s, index-1) - 1
}

// Helper lemma to ensure balance properties
lemma BalanceUpdate(s: string, index: int)
  requires 0 <= index < |s|
  requires IsParenthesesString(s)
  ensures BalanceUpTo(s, index + 1) == BalanceUpTo(s, index) + (if s[index] == '(' then 1 else -1)
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def is_nested(string: str) -> Bool
Create a function that takes a string as input which contains only parentheses. The function should return True if and only if there is a valid subsequence of parentheses where at least one parenthesis in the subsequence is nested.
*/
// </vc-description>

// <vc-spec>
method IsNested(s: string) returns (result: bool)
  requires IsParenthesesString(s)
  ensures result == exists i :: 0 <= i < |s| && s[i] == ')' && BalanceUpTo(s, i) > 0
// </vc-spec>
// <vc-code>
{
  var balance := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant balance == BalanceUpTo(s, i)
    invariant forall k :: 0 <= k < i ==> (s[k] == ')' ==> BalanceUpTo(s, k) > 0 || BalanceUpTo(s, k) == 0)
  {
    if s[i] == '(' {
      balance := balance + 1;
    } else {
      if balance > 0 {
        return true;
      }
      balance := balance - 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
