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
/* helper modified by LLM (iteration 2): adjusted helper function behavior to align with expected postcondition by modifying the return logic */
function ReplaceChars_helper(str1: seq<char>, oldChar: char, newChar: char, i: int): seq<char>
    requires 0 <= i <= |str1|
    ensures |ReplaceChars_helper(str1, oldChar, newChar, i)| == i
    ensures forall k :: 0 <= k < i ==> ReplaceChars_helper(str1, oldChar, newChar, i)[k] == InnerExprReplaceChars(str1, oldChar, newChar, k)
{
    if i == 0 then
        []
    else
        ReplaceChars_helper(str1, oldChar, newChar, i - 1) + [InnerExprReplaceChars(str1, oldChar, newChar, i - 1)]
}
// </vc-helpers>

// <vc-spec>
method ReplaceChars(str1: seq<char>, oldChar: char, newChar: char) returns (result: seq<char>)
    ensures |str1| == |result|
    ensures forall i :: 0 <= i < |str1| ==> result[i] == InnerExprReplaceChars(str1, oldChar, newChar, i)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): call helper function to initialize result */
{
    result := ReplaceChars_helper(str1, oldChar, newChar, |str1|);
}
// </vc-code>
