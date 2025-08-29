// <vc-helpers>
predicate ValidParentheses(s: string)
{
  ValidParenthesesHelper(s, 0)
}

predicate ValidParenthesesHelper(s: string, balance: int)
  decreases |s|
{
  if |s| == 0 then balance == 0
  else if balance < 0 then false
  else if s[0] == '(' then ValidParenthesesHelper(s[1..], balance + 1)
  else if s[0] == ')' then ValidParenthesesHelper(s[1..], balance - 1)
  else ValidParenthesesHelper(s[1..], balance)
}

predicate HasNestedParentheses(s: string)
{
  exists i, j :: 0 <= i < j < |s| && s[i] == '(' && s[j] == ')' &&
    exists k, l :: i < k < l < j && s[k] == '(' && s[l] == ')'
}

predicate OnlyParentheses(s: string)
{
  forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')'
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
  requires OnlyParentheses(s)
  ensures result <==> (ValidParentheses(s) && HasNestedParentheses(s))
// </vc-spec>
// <vc-code>
{
  if |s| < 4 {
    return false;
  }
  
  var balance := 0;
  var maxDepth := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant balance >= 0
    invariant maxDepth >= 0
  {
    if s[i] == '(' {
      balance := balance + 1;
      if balance > maxDepth {
        maxDepth := balance;
      }
    } else if s[i] == ')' {
      if balance == 0 {
        return false;
      }
      balance := balance - 1;
    }
    i := i + 1;
  }
  
  result := balance == 0 && maxDepth >= 2;
}
// </vc-code>
