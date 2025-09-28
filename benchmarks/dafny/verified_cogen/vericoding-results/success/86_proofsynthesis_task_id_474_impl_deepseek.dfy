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
/* helper modified by LLM (iteration 5): Remove duplicate InnerExprReplaceChars and simplify lemma */
lemma ArrayElementLemma(s1: seq<char>, s2: seq<char>, oldChar: char, newChar: char, n: int)
  requires |s1| == |s2|
  requires n <= |s1|
  requires forall i :: 0 <= i < n ==> s2[i] == InnerExprReplaceChars(s1, oldChar, newChar, i)
  ensures forall i :: 0 <= i < n ==> s2[i] == InnerExprReplaceChars(s1, oldChar, newChar, i)
{
}
// </vc-helpers>

// <vc-spec>
method ReplaceChars(str1: seq<char>, oldChar: char, newChar: char) returns (result: seq<char>)
    ensures |str1| == |result|
    ensures forall i :: 0 <= i < |str1| ==> result[i] == InnerExprReplaceChars(str1, oldChar, newChar, i)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Loop-based sequence construction with proper invariants */
{
  result := [];
  var index := 0;
  while index < |str1|
    invariant |result| == index
    invariant index <= |str1|
    invariant forall j :: 0 <= j < index ==> result[j] == InnerExprReplaceChars(str1, oldChar, newChar, j)
  {
    result := result + [InnerExprReplaceChars(str1, oldChar, newChar, index)];
    index := index + 1;
  }
}
// </vc-code>
