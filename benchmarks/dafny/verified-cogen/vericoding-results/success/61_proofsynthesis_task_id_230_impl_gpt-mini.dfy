// <vc-preamble>
function InnerExprReplaceBlanksWithChars(str1: seq<char>, ch: char, i: int): char
    requires 0 <= i < |str1|
{
    if str1[i] == ' ' then
        ch
    else
        str1[i]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): provide CharAtIfBlank helper equivalent to InnerExprReplaceBlanksWithChars */
function CharAtIfBlank(str1: seq<char>, ch: char, i: int): char
  requires 0 <= i < |str1|
{
  if str1[i] == ' ' then ch else str1[i]
}
// </vc-helpers>

// <vc-spec>
method ReplaceBlanksWithChars(str1: seq<char>, ch: char) returns (result: seq<char>)
    ensures
        |str1| == |result| &&
        forall i :: 0 <= i < |str1| ==> result[i] == InnerExprReplaceBlanksWithChars(str1, ch, i)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): build array with loop invariants using InnerExprReplaceBlanksWithChars */
  var a := new char[|str1|];
  var i := 0;
  while i < |str1|
    invariant 0 <= i <= |str1|
    invariant forall j :: 0 <= j < i ==> a[j] == InnerExprReplaceBlanksWithChars(str1, ch, j)
  {
    a[i] := InnerExprReplaceBlanksWithChars(str1, ch, i);
    i := i + 1;
  }
  assert i == |str1|;
  assert forall j :: 0 <= j < |str1| ==> a[j] == InnerExprReplaceBlanksWithChars(str1, ch, j);
  result := a[..];
}
// </vc-code>
