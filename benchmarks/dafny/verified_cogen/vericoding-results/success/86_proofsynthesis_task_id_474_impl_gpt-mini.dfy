// <vc-preamble>
function InnerExprReplaceChars(str1: seq<char>, oldChar: char, newChar: char, i: int): char
    requires 0 <= i < |str1|
{
    if str1[i] == oldChar then
        newChar
    else
        str1[i]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): compute replaced character at index */
function ReplaceCharExpr(str1: seq<char>, oldChar: char, newChar: char, i: int): char
    requires 0 <= i < |str1|
{
    if str1[i] == oldChar then
        newChar
    else
        str1[i]
}
// </vc-helpers>

// <vc-spec>
method ReplaceChars(str1: seq<char>, oldChar: char, newChar: char) returns (result: seq<char>)
    ensures |str1| == |result|
    ensures forall i :: 0 <= i < |str1| ==> result[i] == InnerExprReplaceChars(str1, oldChar, newChar, i)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): build result by populating a mutable array and converting to seq */
  var n := |str1|;
  var a := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == InnerExprReplaceChars(str1, oldChar, newChar, j)
  {
    a[i] := InnerExprReplaceChars(str1, oldChar, newChar, i);
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
