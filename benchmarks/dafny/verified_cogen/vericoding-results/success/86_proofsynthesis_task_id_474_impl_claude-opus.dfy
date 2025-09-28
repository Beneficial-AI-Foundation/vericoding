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

// </vc-helpers>

// <vc-spec>
method ReplaceChars(str1: seq<char>, oldChar: char, newChar: char) returns (result: seq<char>)
    ensures |str1| == |result|
    ensures forall i :: 0 <= i < |str1| ==> result[i] == InnerExprReplaceChars(str1, oldChar, newChar, i)
// </vc-spec>
// <vc-code>
{
  result := [];
  var j := 0;
  while j < |str1|
    invariant 0 <= j <= |str1|
    invariant |result| == j
    invariant forall i :: 0 <= i < j ==> result[i] == InnerExprReplaceChars(str1, oldChar, newChar, i)
  {
    var c := if str1[j] == oldChar then newChar else str1[j];
    result := result + [c];
    j := j + 1;
  }
}
// </vc-code>
