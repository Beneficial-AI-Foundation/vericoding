// <vc-preamble>
predicate IsSpaceCommaDotSpec(c: char)
{
    (c == ' ') || (c == ',') || (c == '.')
}

function InnerExprReplaceWithColon(str1: seq<char>, k: int): char
    requires 0 <= k < |str1|
{
    if IsSpaceCommaDotSpec(str1[k]) then
        ':'
    else
        str1[k]
}
// </vc-preamble>

// <vc-helpers>
function ReplaceChar(c: char): char
{
    if IsSpaceCommaDotSpec(c) then ':' else c
}

lemma ReplaceCharCorrect(str1: seq<char>, k: int)
    requires 0 <= k < |str1|
    ensures ReplaceChar(str1[k]) == InnerExprReplaceWithColon(str1, k)
{
}
// </vc-helpers>

// <vc-spec>
method ReplaceWithColon(str1: seq<char>) returns (result: seq<char>)
    ensures
        |str1| == |result| &&
        forall k :: 0 <= k < |result| ==> result[k] == InnerExprReplaceWithColon(str1, k)
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    while i < |str1|
        invariant 0 <= i <= |str1|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> result[k] == InnerExprReplaceWithColon(str1, k)
    {
        ReplaceCharCorrect(str1, i);
        result := result + [ReplaceChar(str1[i])];
        i := i + 1;
    }
}
// </vc-code>
