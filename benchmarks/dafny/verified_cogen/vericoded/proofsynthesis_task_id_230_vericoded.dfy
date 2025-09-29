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

// </vc-helpers>

// <vc-spec>
method ReplaceBlanksWithChars(str1: seq<char>, ch: char) returns (result: seq<char>)
    ensures
        |str1| == |result| &&
        forall i :: 0 <= i < |str1| ==> result[i] == InnerExprReplaceBlanksWithChars(str1, ch, i)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |str1|
    invariant 0 <= i <= |str1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == InnerExprReplaceBlanksWithChars(str1, ch, j)
  {
    if str1[i] == ' ' {
      result := result + [ch];
    } else {
      result := result + [str1[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
