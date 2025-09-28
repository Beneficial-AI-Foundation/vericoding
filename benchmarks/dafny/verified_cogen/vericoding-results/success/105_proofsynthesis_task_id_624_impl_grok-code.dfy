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

// </vc-helpers>

// <vc-spec>
method ToUppercase(str1: seq<char>) returns (result: seq<char>)
    ensures
        |str1| == |result| &&
        forall i :: 0 <= i < |str1| ==> result[i] == InnerExprToUppercase(str1, i)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed duplicate variable name by renaming local variable to res and assigning to result at end */
  var res: seq<char> := [];
  for i := 0 to |str1|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == InnerExprToUppercase(str1, j)
  {
    res := res + [InnerExprToUppercase(str1, i)];
  }
  result := res;
}
// </vc-code>
