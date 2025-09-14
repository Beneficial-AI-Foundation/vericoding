// <vc-preamble>
predicate IsLowerCase(c: char)
{
    c >= 'a' && c <= 'z'
}

function ShiftMinus32Spec(c: char): char
    requires IsLowerCase(c)
{
    (c as int - 32) as char
}

function InnerExprToUppercase(str1: seq<char>, i: int): char
    requires 0 <= i < |str1|
{
    if IsLowerCase(str1[i]) then
        ShiftMinus32Spec(str1[i])
    else
        str1[i]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */
// </vc-helpers>

// <vc-spec>
method ToUppercase(str1: seq<char>) returns (result: seq<char>)
    ensures
        |str1| == |result| &&
        forall i :: 0 <= i < |str1| ==> result[i] == InnerExprToUppercase(str1, i)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Adjusted loop bound for empty string case and ensured loop invariant for full range. */
{
  var s := new char[|str1|];
  for i := 0 to |str1|
    invariant 0 <= i <= |str1|
    invariant forall j :: 0 <= j < i ==> s[j] == InnerExprToUppercase(str1, j)
  {
    if i < |str1| {
      s[i] := InnerExprToUppercase(str1, i);
    }
  }
  return s[..];
}
// </vc-code>
