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
    /* code modified by LLM (iteration 2): using loop to build sequence and ensure precondition */
    result := [];
    var i := 0;
    while i < |str1|
        invariant 0 <= i <= |str1|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == InnerExprReplaceChars(str1, oldChar, newChar, j)
    {
        result := result + [InnerExprReplaceChars(str1, oldChar, newChar, i)];
        i := i + 1;
    }
}
// </vc-code>
