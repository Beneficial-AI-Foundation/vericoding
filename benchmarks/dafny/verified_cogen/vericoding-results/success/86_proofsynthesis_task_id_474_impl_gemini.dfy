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
  /* code modified by LLM (iteration 4): Replaced the failing sequence constructor with a while loop to build the sequence manually and guide the verifier. */
  result := [];
  var i := 0;
  while i < |str1|
    invariant 0 <= i <= |str1|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == InnerExprReplaceChars(str1, oldChar, newChar, k)
  {
    // The loop invariant 0 <= i and guard i < |str1| satisfy the precondition of InnerExprReplaceChars.
    var next_char := InnerExprReplaceChars(str1, oldChar, newChar, i);
    result := result + [next_char];
    i := i + 1;
  }
}
// </vc-code>
